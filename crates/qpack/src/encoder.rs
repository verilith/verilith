//! The verified encoder: field sections (`encode`), the encoder stream it
//! writes (`take_output`), and the decoder stream it reads
//! (`feed_decoder`).
//!
//! What is proven (see `Encoder::inv`): the encoder stream written so far,
//! run by the spec decoder from an empty table, gives exactly the
//! encoder's table; each field section, decoded by the spec with that
//! table, gives back the fields encoded; and the encoder keeps the
//! obligations of RFC 9204 to the decoder (`spec::enc_ok`): the capacity
//! limit, no eviction of an entry that is unacknowledged or that an
//! unacknowledged section references, and the blocked-stream limit.
//!
//! Which representation to use is decided with hints (`Hints`,
//! `static_find`): hash lookups that are not verified and need not be
//! right, since every hint is checked, byte for byte, before it is used.
use crate::decoder::to_vec;
use crate::fields::Fields;
use crate::henc;
use crate::integer::{self, IntE, P2};
use crate::strings::EndE;
#[cfg(verus_only)]
use crate::integer::lemma_pows;
use crate::rt::*;
use crate::spec::*;
use crate::table::*;
use crate::lemmas::*;
use std::rc::Rc;
use verilith_core::prims::extend;
use vstd::prelude::*;

verus! {

/// `a == b`.
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// Writes the `n`-bit prefix string literal of `s` under `flags`,
/// Huffman-coding it when that is shorter.
pub fn write_str(out: &mut Vec<u8>, flags: u8, n: u8, s: &[u8]) -> (r: (Ghost<bool>, Ghost<Seq<u8>>))
    requires
        2 <= n <= 8,
        (flags as nat) % p2(n as nat) == 0,
        henc::code_ok(),
        s@.len() <= 0x1000_0000,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        str_ok(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), flags as nat, n as nat, s@, r.0@, r.1@),
        r.1@.len() <= s@.len(),
{
    let ghost o0 = out@;
    let ghost z = o0.len() as int;
    proof {
        henc::lemma_hval_bound(s@);
        lemma_pows();
        lemma_p2_vals();
    }
    let bits = henc::bits_of(s);
    let hl = (bits + 7) / 8;
    let m = n - 1;
    proof {
        assert(P2@[m as int] as nat == p2(m as nat));
        assert(p2(n as nat) == 2 * p2(m as nat));
        assert(p2(m as nat) > 0);
    }
    if hl < s.len() as u64 {
        let hf = P2[m as usize] as u8;
        proof {
            lemma_half_mod(flags as nat, p2(m as nat), p2(m as nat));
            integer::lemma_flags(flags as nat, n as nat, p2(m as nat));
        }
        let fl = flags + hf;
        integer::encode(out, fl, m, hl);
        let ghost o1 = out@;
        henc::encode(s, out);
        proof {
            let o2 = out@;
            let ix = int_enc(fl as nat, m as nat, hl as nat);
            let raw = o2.subrange(o1.len() as int, o2.len() as int);
            assert(o1 == o0 + ix);
            assert(o2.subrange(z, o2.len() as int) =~= ix + raw) by {
                assert(o2.subrange(0, o1.len() as int) == o1);
                assert forall|j: int| 0 <= j < ix.len() implies o2[z + j] == ix[j] by {
                    assert(o2[z + j] == o2.subrange(0, o1.len() as int)[z + j]);
                }
            }
            assert(o2.subrange(0, z) =~= o0) by {
                assert(o2.subrange(0, o1.len() as int) == o1);
                assert forall|j: int| 0 <= j < z implies o2[j] == o0[j] by {
                    assert(o2[j] == o2.subrange(0, o1.len() as int)[j]);
                }
            }
            assert(raw.len() == hl);
            assert(fl as nat == flags as nat + p2(m as nat));
        }
        (Ghost(true), Ghost(out@.subrange((o0.len() + int_enc(fl as nat, m as nat, hl as nat).len()) as int, out@.len() as int)))
    } else {
        proof {
            lemma_half_mod(flags as nat, p2(m as nat), 0);
        }
        integer::encode(out, flags, m, s.len() as u64);
        extend(out, s);
        proof {
            let ix = int_enc(flags as nat, m as nat, s@.len());
            assert(out@ == o0 + ix + s@);
            assert(out@.subrange(z, out@.len() as int) =~= ix + s@);
            assert(out@.subrange(0, z) =~= o0);
        }
        (Ghost(false), Ghost(s@))
    }
}

/// Where the static table has `name: value` (the first result) and
/// `name` (the second), as hints: 99 for none.
#[verifier::external_body]
pub fn static_find(name: &[u8], value: &[u8]) -> (usize, usize) {
    crate::hints::static_find(name, value)
}

/// Lookups in the dynamic table, by hash: hints only.
#[verifier::external_body]
pub struct Hints {
    pub h: crate::hints::Index,
}

impl Hints {
    #[verifier::external_body]
    pub fn new() -> Hints {
        Hints { h: crate::hints::Index::new() }
    }

    /// The newest entry that may be `name: value`.
    #[verifier::external_body]
    pub fn find(&self, name: &[u8], value: &[u8]) -> Option<u64> {
        self.h.find(name, value)
    }

    /// Whether `name: value` is worth inserting.
    #[verifier::external_body]
    pub fn worth(&mut self, name: &[u8], value: &[u8]) -> bool {
        self.h.worth(name, value)
    }

    /// Entry `a` is `name: value`; entries below `dropped` are gone.
    #[verifier::external_body]
    pub fn add(&mut self, name: &[u8], value: &[u8], a: u64, dropped: u64) {
        self.h.add(name, value, a, dropped)
    }
}

/// A section not yet acknowledged.
#[derive(Clone, Copy)]
pub struct SentX {
    pub stream: u64,
    pub ric: u64,
    pub min_ref: u64,
}

pub open spec fn sview(v: Seq<SentX>) -> Seq<Sent> {
    Seq::new(v.len(), |i: int| Sent { stream: v[i].stream as nat, ric: v[i].ric as nat, min_ref: v[i].min_ref as nat })
}

pub open spec fn nats(v: Seq<u64>) -> Seq<nat> {
    Seq::new(v.len(), |i: int| v[i] as nat)
}

/// The dynamic table references of the field lines written so far in a
/// section: whether there are any, the lowest and the highest.
#[derive(Clone, Copy)]
pub struct Refs {
    pub has: bool,
    pub min: u64,
    pub max: u64,
}

/// The items written so far in a section, with Base `base`, are right for
/// table `t`, and refer only to entries from `r.min` to `r.max`.
pub open spec fn sec_ok(t: Table, base: nat, r: Refs, its: Seq<Item>) -> bool {
    &&& r.has ==> t.dropped <= r.min <= r.max < icount(t)
    &&& forall|k: int| 0 <= k < its.len() ==> {
        &&& item_ok(t, base, #[trigger] its[k])
        &&& (iref(its[k]) matches Some(a) ==> r.has && r.min <= a <= r.max)
    }
}

/// Largest Insert Count the encoder goes to, short of `MAX_INT`.
pub const MAX_INSERTS: u64 = 0x3FFF_FFFF_FFFF_FF00;

/// Writes the Indexed Field Line for entry `a` of `t` (by relative index
/// below Base, post-base at or above it).
fn emit_idx(lines: &mut Vec<u8>, base: u64, a: u64, Ghost(t): Ghost<Table>) -> (it: Ghost<Item>)
    requires
        abs_ok(t, a as nat),
        base <= icount(t),
    ensures
        item_ok(t, base as nat, it@),
        iref(it@) == Some(a as nat),
        it@.field == (Field { name: abs(t, a as nat).0, value: abs(t, a as nat).1, never: false }),
        final(lines)@ == old(lines)@ + it@.bytes,
{
    proof {
        lemma_p2_vals();
    }
    let f = Ghost(Field { name: abs(t, a as nat).0, value: abs(t, a as nat).1, never: false });
    if a < base {
        integer::encode(lines, 0x80, 6, base - 1 - a);
        Ghost(Item { bytes: int_enc(0x80, 6, (base - 1 - a) as nat), field: f@, kind: Kind::IdxRel(a as nat) })
    } else {
        integer::encode(lines, 0x10, 4, a - base);
        Ghost(Item { bytes: int_enc(0x10, 4, (a - base) as nat), field: f@, kind: Kind::IdxPost(a as nat) })
    }
}

/// Every element of `a` is one of `b`.
pub open spec fn sub(a: Seq<Sent>, b: Seq<Sent>) -> bool {
    forall|j: int| 0 <= j < a.len() ==> b.contains(#[trigger] a[j])
}

pub proof fn lemma_drop_stream_sub(sent: Seq<Sent>, s: nat)
    ensures
        sub(drop_stream(sent, s), sent),
    decreases sent.len(),
{
    if sent.len() > 0 {
        let p = sent.drop_last();
        lemma_drop_stream_sub(p, s);
        let r = drop_stream(p, s);
        let r2 = drop_stream(sent, s);
        assert forall|j: int| 0 <= j < r2.len() implies sent.contains(#[trigger] r2[j]) by {
            if j < r.len() {
                assert(p.contains(r[j]));
                let k = choose|k: int| 0 <= k < p.len() && p[k] == r[j];
                assert(r2[j] == r[j]);
                assert(p[k] == sent[k]);
            } else {
                assert(r2[j] == sent[sent.len() - 1]);
            }
        }
    }
}

pub proof fn lemma_remove_sub(sent: Seq<Sent>, i: int)
    requires
        0 <= i < sent.len(),
    ensures
        sub(sent.remove(i), sent),
{
    let r = sent.remove(i);
    assert forall|j: int| 0 <= j < r.len() implies sent.contains(#[trigger] r[j]) by {
        let k = if j < i { j } else { j + 1 };
        assert(r[j] == sent[k]);
        assert(0 <= k < sent.len());
        assert(r[j] == sent[k]);
    }
}

/// `enc_ok`, and its witness, carry over to fewer sections and a higher
/// Known Received Count.
pub proof fn lemma_enc_ok_sub(st: EncState, sent2: Seq<Sent>, krc2: nat, ss: Seq<nat>)
    requires
        enc_ok(st),
        ss.len() <= st.max_blocked,
        covers(ss, st.sent, st.krc),
        sub(sent2, st.sent),
        st.krc <= krc2 <= icount(st.table),
    ensures
        enc_ok(EncState { sent: sent2, krc: krc2, ..st }),
        covers(ss, sent2, krc2),
{
    let st2 = EncState { sent: sent2, krc: krc2, ..st };
    assert forall|j: int| 0 <= j < sent2.len() implies {
        &&& st.table.dropped <= #[trigger] sent2[j].min_ref
        &&& 0 < sent2[j].ric <= icount(st.table)
        &&& (sent2[j].ric > krc2 ==> ss.contains(sent2[j].stream))
    } by {
        assert(st.sent.contains(sent2[j]));
        let k = choose|k: int| 0 <= k < st.sent.len() && st.sent[k] == sent2[j];
        assert(st.sent[k].min_ref >= st.table.dropped);
        assert(0 < st.sent[k].ric <= icount(st.table));
    }
    assert(covers(ss, sent2, krc2));
}

pub proof fn lemma_first_of(sent: Seq<Sent>, s: nat, i: int)
    requires
        0 <= i < sent.len(),
        sent[i].stream == s,
        forall|j: int| 0 <= j < i ==> #[trigger] sent[j].stream != s,
    ensures
        first_of(sent, s) == Some(i),
{
    let c = choose|c: int| 0 <= c < sent.len() && #[trigger] sent[c].stream == s
        && forall|j: int| 0 <= j < c ==> #[trigger] sent[j].stream != s;
    if c < i {
        assert(sent[c].stream != s);
    } else if c > i {
        assert(sent[i].stream != s);
    }
}

/// Frames the decoder instruction at the start of `b`.
fn dframe_x(b: &[u8]) -> (r: EndE)
    ensures
        match (r, dframe(b@)) {
            (EndE::Short, EndR::Short) => true,
            (EndE::Bad, EndR::Bad) => true,
            (EndE::Ok(e), EndR::Ok(se)) => e as int == se && 0 < e <= b@.len(),
            _ => false,
        },
{
    proof {
        reveal(dframe);
    }
    if b.len() == 0 {
        return EndE::Short;
    }
    let n: u8 = if b[0] >= 0x80 { 7 } else { 6 };
    match integer::decode(b, 0, n) {
        IntE::Short => EndE::Short,
        IntE::Bad => EndE::Bad,
        IntE::Ok(_, e) => EndE::Ok(e),
    }
}

/// A QPACK encoder (one per HTTP/3 connection): it writes field sections
/// and the encoder stream, and reads the peer's decoder stream.
pub struct Encoder {
    pub table: DynTable,
    /// The peer decoder's SETTINGS_QPACK_MAX_TABLE_CAPACITY.
    pub max_cap: u64,
    /// The peer decoder's SETTINGS_QPACK_BLOCKED_STREAMS.
    pub max_blocked: u64,
    /// The Known Received Count.
    pub krc: u64,
    /// The sections not yet acknowledged, oldest first.
    pub sent: Vec<SentX>,
    /// Streams that may have a section that could block: at most
    /// `max_blocked`, and every such stream is here.
    pub risky: Vec<u64>,
    /// Encoder stream bytes not yet taken.
    pub es: Vec<u8>,
    /// The start of a decoder instruction that has not fully arrived.
    pub held: Vec<u8>,
    pub hints: Hints,
    /// The whole encoder stream so far, and the part taken.
    pub es_all: Ghost<Seq<u8>>,
    pub taken: Ghost<Seq<u8>>,
}

impl Encoder {
    pub open spec fn state(&self) -> EncState {
        EncState {
            table: self.table.view(),
            max_cap: self.max_cap as nat,
            max_blocked: self.max_blocked as nat,
            krc: self.krc as nat,
            sent: sview(self.sent@),
        }
    }

    /// The invariant: the encoder's obligations (`enc_ok`), and the
    /// encoder stream so far, run from an empty table, gives its table.
    pub open spec fn inv(&self) -> bool {
        &&& self.table.inv()
        &&& self.max_cap <= CAP_LIMIT
        &&& henc::code_ok()
        &&& enc_ok(self.state())
        &&& self.risky@.len() <= self.max_blocked
        &&& covers(nats(self.risky@), sview(self.sent@), self.krc as nat)
        &&& icount(self.table.view()) <= MAX_INSERTS
        &&& erun(empty_table(), self.max_cap as nat, self.es_all@) == Run::Ok(self.table.view(), self.es_all@.len() as int)
        &&& self.es_all@ == self.taken@ + self.es@
        &&& dframe(self.held@) is Short
    }

    /// An encoder for a peer that sent `max_cap` and `max_blocked`, using
    /// a table of `cap` bytes (at most `max_cap`; 0 for no dynamic table).
    pub fn new(max_cap: u64, max_blocked: u64, cap: u64) -> (r: Option<Encoder>)
        ensures
            r matches Some(e) ==> e.inv() && e.max_cap == max_cap && e.max_blocked == max_blocked
                && e.taken@ == Seq::<u8>::empty() && e.state().sent.len() == 0,
    {
        if max_cap > CAP_LIMIT || cap > max_cap || !henc::check() {
            return None;
        }
        let mut e = Encoder {
            table: DynTable::new(),
            max_cap,
            max_blocked,
            krc: 0,
            sent: Vec::new(),
            risky: Vec::new(),
            es: Vec::new(),
            held: Vec::new(),
            hints: Hints::new(),
            es_all: Ghost(Seq::empty()),
            taken: Ghost(Seq::empty()),
        };
        proof {
            reveal(dframe);
            reveal(eframe);
            assert(erun(empty_table(), max_cap as nat, Seq::<u8>::empty()) == Run::Ok(empty_table(), 0));
            assert(covers(nats(e.risky@), sview(e.sent@), 0));
            assert(e.es_all@ =~= e.taken@ + e.es@);
        }
        if cap > 0 {
            proof {
                lemma_p2_vals();
            }
            integer::encode(&mut e.es, 0x20, 5, cap);
            let ghost t0 = e.table.view();
            e.table.set_cap(cap);
            proof {
                lemma_p2_vals();
                let x = Ins { bytes: e.es@, kind: IKind::SetCap(cap as nat), entry: (Seq::empty(), Seq::empty()) };
                assert(e.es@ =~= int_enc(0x20, 5, cap as nat));
                lemma_erun_ins(t0, max_cap as nat, x);
                lemma_evict(t0, 0, cap as nat);
            }
            e.es_all = Ghost(e.es@);
            proof {
                assert(e.es_all@ =~= e.taken@ + e.es@);
            }
        }
        proof {
            assert(covers(nats(e.risky@), e.state().sent, e.state().krc));
            assert(e.table.inv());
            assert(enc_ok(e.state()));
            assert(erun(empty_table(), e.max_cap as nat, e.es_all@) == Run::Ok(e.table.view(), e.es_all@.len() as int));
            assert(e.es_all@ == e.taken@ + e.es@);
            assert(dframe(e.held@) is Short);
            assert(icount(e.table.view()) <= MAX_INSERTS);
        }
        Some(e)
    }

    /// Hands over the encoder stream bytes written so far.
    pub fn take_output(&mut self, dst: &mut Vec<u8>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(dst)@ == old(dst)@ + old(self).es@,
            final(self).taken@ == old(self).taken@ + old(self).es@,
            final(self).es_all@ == old(self).es_all@,
            final(self).state() == old(self).state(),
    {
        extend(dst, self.es.as_slice());
        self.taken = Ghost(self.taken@ + self.es@);
        self.es.clear();
        proof {
            assert(self.es_all@ =~= self.taken@ + self.es@);
        }
    }

    /// Whether a section on `stream` may block (§2.1.2).
    fn can_block(&self, stream: u64) -> (r: bool)
        ensures
            r == (nats(self.risky@).contains(stream as nat) || self.risky@.len() < self.max_blocked),
    {
        if (self.risky.len() as u64) < self.max_blocked {
            return true;
        }
        let mut i: usize = 0;
        while i < self.risky.len()
            invariant
                i <= self.risky@.len(),
                forall|j: int| 0 <= j < i ==> self.risky@[j] != stream,
            decreases self.risky@.len() - i,
        {
            if self.risky[i] == stream {
                proof {
                    assert(nats(self.risky@)[i as int] == stream as nat);
                }
                return true;
            }
            i = i + 1;
        }
        proof {
            if nats(self.risky@).contains(stream as nat) {
                let j = choose|j: int| 0 <= j < nats(self.risky@).len() && nats(self.risky@)[j] == stream as nat;
                assert(self.risky@[j] == stream);
            }
        }
        false
    }

    /// The lowest entry an unacknowledged section references (or more).
    fn min_sent(&self) -> (r: u64)
        ensures
            forall|i: int| 0 <= i < self.sent@.len() ==> r <= #[trigger] self.sent@[i].min_ref,
    {
        let mut m: u64 = u64::MAX;
        let mut i: usize = 0;
        while i < self.sent.len()
            invariant
                i <= self.sent@.len(),
                forall|j: int| 0 <= j < i ==> m <= #[trigger] self.sent@[j].min_ref,
            decreases self.sent@.len() - i,
        {
            if self.sent[i].min_ref < m {
                m = self.sent[i].min_ref;
            }
            i = i + 1;
        }
        m
    }

    /// The obligations an insert must keep: entry `d` and above stay.
    pub open spec fn same_but_table(&self, o: &Encoder) -> bool {
        &&& self.max_cap == o.max_cap
        &&& self.max_blocked == o.max_blocked
        &&& self.krc == o.krc
        &&& self.sent@ == o.sent@
        &&& self.risky@ == o.risky@
        &&& self.taken@ == o.taken@
        &&& self.held@ == o.held@
    }

    /// Inserts `name: value` (by static name reference `sn`, or with a
    /// literal name if `sn` is 99), writing the instruction, if it fits and
    /// evicts nothing at or above `limit` nor anything unacknowledged.
    fn insert_field(&mut self, name: &[u8], value: &[u8], sn: usize, limit: u64) -> (r: bool)
        requires
            old(self).inv(),
            sn < 99 ==> static_name(sn as int) == name@,
            name@.len() + value@.len() <= 0x1000_0000,
            forall|i: int| 0 <= i < old(self).sent@.len() ==> limit <= #[trigger] old(self).sent@[i].min_ref,
        ensures
            final(self).inv(),
            final(self).same_but_table(old(self)),
            keeps(old(self).table.view(), final(self).table.view()),
            final(self).table.view().dropped <= limit || final(self).table.view() == old(self).table.view(),
            r ==> icount(final(self).table.view()) == icount(old(self).table.view()) + 1
                && abs(final(self).table.view(), icount(old(self).table.view())) == (name@, value@)
                && final(self).table.view().dropped <= limit,
            !r ==> final(self).table.view() == old(self).table.view(),
    {
        let ghost t0 = self.table.view();
        proof {
            assert(keeps(t0, t0));
        }
        let es_sz = name.len() as u64 + value.len() as u64 + 32;
        if es_sz > self.table.cap || self.table.icount() >= MAX_INSERTS {
            return false;
        }
        let d = self.table.dropped_after(es_sz);
        if d > self.krc || d > limit {
            return false;
        }
        let ghost e0 = self.es@;
        let ghost mc = self.max_cap as nat;
        let ghost ent: Entry = (name@, value@);
        proof {
            lemma_p2_vals();
        }
        let ghost x: Ins;
        if sn < 99 {
            integer::encode(&mut self.es, 0xC0, 6, sn as u64);
            let ghost e1 = self.es@;
            let (h, raw) = write_str(&mut self.es, 0, 8, value);
            proof {
                let ix = int_enc(0xC0, 6, sn as nat);
                let e2 = self.es@;
                let bytes = e2.subrange(e0.len() as int, e2.len() as int);
                assert(e1 == e0 + ix);
                assert(bytes.subrange(0, ix.len() as int) =~= ix) by {
                    assert forall|j: int| 0 <= j < ix.len() implies bytes[j] == ix[j] by {
                        assert(e2.subrange(0, e1.len() as int)[e0.len() + j] == e1[e0.len() + j]);
                    }
                }
                assert(bytes.subrange(ix.len() as int, bytes.len() as int) =~= e2.subrange(e1.len() as int, e2.len() as int));
                x = Ins { bytes, kind: IKind::InsStatic(sn as nat, h@, raw@), entry: ent };
                assert(raw@.len() <= str_limit(mc));
                assert(e2 =~= e0 + bytes) by {
                    assert forall|j: int| 0 <= j < e0.len() implies e2[j] == e0[j] by {
                        assert(e2.subrange(0, e1.len() as int)[j] == e1[j]);
                    }
                }
            }
        } else {
            let (hn, rn) = write_str(&mut self.es, 0x40, 6, name);
            let ghost e1 = self.es@;
            let (hv, rv) = write_str(&mut self.es, 0, 8, value);
            proof {
                let e2 = self.es@;
                let bytes = e2.subrange(e0.len() as int, e2.len() as int);
                let k = e1.len() - e0.len();
                assert(bytes.subrange(0, k) =~= e1.subrange(e0.len() as int, e1.len() as int)) by {
                    assert forall|j: int| 0 <= j < k implies bytes[j] == e1[e0.len() + j] by {
                        assert(e2.subrange(0, e1.len() as int)[e0.len() + j] == e1[e0.len() + j]);
                    }
                }
                assert(bytes.subrange(k, bytes.len() as int) =~= e2.subrange(e1.len() as int, e2.len() as int));
                x = Ins { bytes, kind: IKind::InsLit(hn@, rn@, hv@, rv@), entry: ent };
                assert(str_ok(x.bytes.subrange(0, k), 0x40, 6, x.entry.0, hn@, rn@));
                assert(e2 =~= e0 + bytes) by {
                    assert forall|j: int| 0 <= j < e0.len() implies e2[j] == e0[j] by {
                        assert(e2.subrange(0, e1.len() as int)[j] == e1[j]);
                    }
                }
            }
        }
        let ent_x = Ent { name: Rc::new(to_vec(name)), value: Rc::new(to_vec(value)) };
        proof {
            assert(ent_x.view() == ent);
            assert(ins_ok(t0, mc, x));
            assert(insert(t0, ent) is Some);
        }
        let (ok, _) = self.table.insert(ent_x);
        proof {
            assert(ok);
            lemma_erun_ins(t0, mc, x);
            lemma_erun_cat(empty_table(), mc, self.es_all@, x.bytes, t0, self.table.view());
            lemma_keeps_apply(t0, x);
            lemma_evict(t0, esize(ent), t0.cap);
        }
        self.es_all = Ghost(self.es_all@ + x.bytes);
        proof {
            assert(self.es_all@ =~= self.taken@ + self.es@);
            let st = self.state();
            assert forall|i: int| 0 <= i < st.sent.len() implies st.table.dropped <= #[trigger] st.sent[i].min_ref by {
                assert(limit <= old(self).sent@[i].min_ref);
            }
            assert(covers(nats(self.risky@), self.state().sent, self.state().krc));
        }
        true
    }

    /// Writes one field line of a section with Base `base`, inserting the
    /// field first when that is allowed and worth it. `refs` are the
    /// section's references so far; the result adds this line's.
    fn line(&mut self, name: &[u8], value: &[u8], never: bool, base: u64, can_block: bool, min_sent: u64, refs: Refs, lines: &mut Vec<u8>) -> (r: (Refs, Ghost<Item>))
        requires
            old(self).inv(),
            base <= icount(old(self).table.view()),
            forall|i: int| 0 <= i < old(self).sent@.len() ==> min_sent <= #[trigger] old(self).sent@[i].min_ref,
            refs.has ==> old(self).table.view().dropped <= refs.min <= refs.max < icount(old(self).table.view()),
            refs.has && refs.max >= old(self).krc ==> can_block,
            name@.len() + value@.len() <= 0x1000_0000,
        ensures
            final(self).inv(),
            final(self).same_but_table(old(self)),
            keeps(old(self).table.view(), final(self).table.view()),
            refs.has ==> final(self).table.view().dropped <= refs.min,
            r.0.has ==> final(self).table.view().dropped <= r.0.min <= r.0.max < icount(final(self).table.view()),
            refs.has ==> r.0.has && r.0.min <= refs.min && r.0.max >= refs.max,
            r.0.has && r.0.max >= old(self).krc ==> can_block,
            item_ok(final(self).table.view(), base as nat, r.1@),
            iref(r.1@) matches Some(a) ==> r.0.has && r.0.min <= a <= r.0.max,
            r.1@.field == (Field { name: name@, value: value@, never }),
            final(lines)@ == old(lines)@ + r.1@.bytes,
    {
        let ghost t0 = self.table.view();
        let ghost f = Field { name: name@, value: value@, never };
        proof {
            lemma_p2_vals();
            assert(keeps(t0, t0));
        }
        let (si, sn0) = static_find(name, value);
        let mut sn: usize = 99;
        if sn0 < 99 {
            let (n2, _) = static_entry(sn0);
            if bytes_eq(n2, name) {
                sn = sn0;
            }
        }
        if !never && si < 99 {
            let (n2, v2) = static_entry(si);
            if bytes_eq(n2, name) && bytes_eq(v2, value) {
                integer::encode(lines, 0xC0, 6, si as u64);
                return (refs, Ghost(Item { bytes: int_enc(0xC0, 6, si as nat), field: f, kind: Kind::IdxStatic(si as nat) }));
            }
        }
        if !never {
            match self.hints.find(name, value) {
                Some(a) => {
                    if a >= self.table.dropped && a < self.table.icount() && (a < self.krc || can_block) {
                        let e = self.table.abs(a);
                        if bytes_eq(e.name.as_slice(), name) && bytes_eq(e.value.as_slice(), value) {
                            let r2 = Refs {
                                has: true,
                                min: if refs.has && refs.min < a { refs.min } else { a },
                                max: if refs.has && refs.max > a { refs.max } else { a },
                            };
                            let it = emit_idx(lines, base, a, Ghost(t0));
                            return (r2, it);
                        }
                    }
                },
                None => {},
            }
        }
        if !never && can_block && self.hints.worth(name, value) {
            let limit = if refs.has && refs.min < min_sent { refs.min } else { min_sent };
            let a = self.table.icount();
            if self.insert_field(name, value, sn, limit) {
                let ghost t1 = self.table.view();
                let d = self.table.dropped;
                self.hints.add(name, value, a, d);
                let r2 = Refs { has: true, min: if refs.has { refs.min } else { a }, max: a };
                let it = emit_idx(lines, base, a, Ghost(t1));
                return (r2, it);
            }
        }
        let ghost l0 = lines@;
        if sn < 99 {
            let fl: u8 = if never { 0x70 } else { 0x50 };
            integer::encode(lines, fl, 4, sn as u64);
            let ghost l1 = lines@;
            let (h, raw) = write_str(lines, 0, 8, value);
            let ghost it: Item;
            proof {
                let ix = int_enc(fl as nat, 4, sn as nat);
                let l2 = lines@;
                let bytes = l2.subrange(l0.len() as int, l2.len() as int);
                assert(l1 == l0 + ix);
                assert(bytes.subrange(0, ix.len() as int) =~= ix) by {
                    assert forall|j: int| 0 <= j < ix.len() implies bytes[j] == ix[j] by {
                        assert(l2.subrange(0, l1.len() as int)[l0.len() + j] == l1[l0.len() + j]);
                    }
                }
                assert(bytes.subrange(ix.len() as int, bytes.len() as int) =~= l2.subrange(l1.len() as int, l2.len() as int));
                assert(l2 =~= l0 + bytes) by {
                    assert forall|j: int| 0 <= j < l0.len() implies l2[j] == l0[j] by {
                        assert(l2.subrange(0, l1.len() as int)[j] == l1[j]);
                    }
                }
                assert(fl as nat == 0x50 + never_bits(never, 0x20));
                it = Item { bytes, field: f, kind: Kind::LitStatic(sn as nat, h@, raw@) };
                assert(item_ok(t0, base as nat, it));
            }
            (refs, Ghost(it))
        } else {
            let fl: u8 = if never { 0x30 } else { 0x20 };
            let (hn, rn) = write_str(lines, fl, 4, name);
            let ghost l1 = lines@;
            let (hv, rv) = write_str(lines, 0, 8, value);
            let ghost it: Item;
            proof {
                let l2 = lines@;
                let bytes = l2.subrange(l0.len() as int, l2.len() as int);
                let k = l1.len() - l0.len();
                assert(bytes.subrange(0, k) =~= l1.subrange(l0.len() as int, l1.len() as int)) by {
                    assert forall|j: int| 0 <= j < k implies bytes[j] == l1[l0.len() + j] by {
                        assert(l2.subrange(0, l1.len() as int)[l0.len() + j] == l1[l0.len() + j]);
                    }
                }
                assert(bytes.subrange(k, bytes.len() as int) =~= l2.subrange(l1.len() as int, l2.len() as int));
                assert(l2 =~= l0 + bytes) by {
                    assert forall|j: int| 0 <= j < l0.len() implies l2[j] == l0[j] by {
                        assert(l2.subrange(0, l1.len() as int)[j] == l1[j]);
                    }
                }
                assert(fl as nat == 0x20 + never_bits(never, 0x10));
                it = Item { bytes, field: f, kind: Kind::LitLit(hn@, rn@, hv@, rv@) };
                assert(str_ok(it.bytes.subrange(0, k), 0x20 + never_bits(it.field.never, 0x10), 4, it.field.name, hn@, rn@));
                assert(item_ok(t0, base as nat, it));
            }
            (refs, Ghost(it))
        }
    }

    /// Encodes the field section `fields` for stream `stream`, appending
    /// it to `out` (the encoder instructions it needs go to the encoder
    /// stream). The result is its Required Insert Count. Proven: the spec
    /// decoder, with the encoder's table, decodes the section to `fields`
    /// under any size limit that allows them.
    pub fn encode(&mut self, stream: u64, fields: &Fields, out: &mut Vec<u8>) -> (r: Ghost<nat>)
        requires
            old(self).inv(),
            fields.inv(),
            fields.buf@.len() <= 0x1000_0000,
        ensures
            final(self).inv(),
            final(self).max_cap == old(self).max_cap,
            final(self).taken@ == old(self).taken@,
            final(self).held@ == old(self).held@,
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
            forall|ms: nat| ms >= fsizes(fields.view()) ==> #[trigger] section(final(self).table.view(), final(self).max_cap as nat, ms,
                final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int)) == SecR::Ok(fields.view(), r@),
    {
        if self.risky.len() as u64 >= self.max_blocked && self.max_blocked > 0 {
            self.prune_risky();
        }
        self.encode_inner(stream, fields, out)
    }

    #[verifier::spinoff_prover]
    fn encode_inner(&mut self, stream: u64, fields: &Fields, out: &mut Vec<u8>) -> (r: Ghost<nat>)
        requires
            old(self).inv(),
            fields.inv(),
            fields.buf@.len() <= 0x1000_0000,
        ensures
            final(self).inv(),
            final(self).max_cap == old(self).max_cap,
            final(self).taken@ == old(self).taken@,
            final(self).held@ == old(self).held@,
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
            forall|ms: nat| ms >= fsizes(fields.view()) ==> #[trigger] section(final(self).table.view(), final(self).max_cap as nat, ms,
                final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int)) == SecR::Ok(fields.view(), r@),
    {
        let base = self.table.icount();
        let can_block = self.can_block(stream);
        let min_sent = self.min_sent();
        let mut lines: Vec<u8> = Vec::new();
        let mut refs = Refs { has: false, min: 0, max: 0 };
        let ghost mut its: Seq<Item> = Seq::empty();
        let n = fields.len();
        let mut i: usize = 0;
        let ghost s0 = *old(self);
        proof {
            assert(lines@ =~= cat(its));
            assert(flds(its) =~= fields.view().take(0));
        }
        while i < n
            invariant
                self.inv(),
                self.same_but_table(&s0),
                s0 == *old(self),
                fields.inv(),
                fields.buf@.len() <= 0x1000_0000,
                n == fields.view().len(),
                i <= n,
                base <= icount(self.table.view()),
                forall|j: int| 0 <= j < self.sent@.len() ==> min_sent <= #[trigger] self.sent@[j].min_ref,
                refs.has && refs.max >= self.krc ==> can_block,
                can_block == (nats(self.risky@).contains(stream as nat) || self.risky@.len() < self.max_blocked),
                sec_ok(self.table.view(), base as nat, refs, its),
                its.len() == i,
                lines@ == cat(its),
                flds(its) == fields.view().take(i as int),
            decreases n - i,
        {
            let (name, value, never) = fields.get(i);
            let ghost t0 = self.table.view();
            let ghost l0 = lines@;
            let (r2, it) = self.line(name, value, never, base, can_block, min_sent, refs, &mut lines);
            proof {
                let t1 = self.table.view();
                assert forall|k: int| 0 <= k < its.len() implies {
                    &&& item_ok(t1, base as nat, #[trigger] its[k])
                    &&& (iref(its[k]) matches Some(a) ==> r2.has && r2.min <= a <= r2.max)
                } by {
                    lemma_item_keeps(t0, t1, base as nat, its[k]);
                }
                let its2 = its.push(it@);
                lemma_cat_push(its, it@);
                assert forall|k: int| 0 <= k < its2.len() implies {
                    &&& item_ok(t1, base as nat, #[trigger] its2[k])
                    &&& (iref(its2[k]) matches Some(a) ==> r2.has && r2.min <= a <= r2.max)
                } by {
                    if k < its.len() {
                        assert(its2[k] == its[k]);
                    }
                }
                assert(flds(its2) =~= fields.view().take(i + 1));
                its = its2;
            }
            refs = r2;
            i = i + 1;
        }
        let ghost t = self.table.view();
        let ghost mc = self.max_cap as nat;
        proof {
            assert(fields.view().take(n as int) =~= fields.view());
            lemma_p2_vals();
        }
        let ric: u64 = if refs.has { refs.max + 1 } else { 0 };
        let bw: u64 = if refs.has { base } else { 0 };
        let me = self.max_cap / 32;
        proof {
            lemma_max_entries(t, mc);
            if refs.has {
                assert(t.ents.len() > 0);
                assert(me > 0);
            }
        }
        let enc_ric: u64 = if ric == 0 { 0 } else { ric % (2 * me) + 1 };
        let ghost o0 = out@;
        integer::encode(out, 0, 8, enc_ric);
        if bw >= ric {
            integer::encode(out, 0, 7, bw - ric);
        } else {
            integer::encode(out, 0x80, 7, ric - bw - 1);
        }
        extend(out, lines.as_slice());
        proof {
            let sb = sec_bytes(ric as nat, bw as nat, mc, its);
            assert(enc_ric as nat == encode_ric(ric as nat, mc));
            assert(out@ =~= o0 + sb);
            assert(out@.subrange(o0.len() as int, out@.len() as int) =~= sb);
            assert(out@.subrange(0, o0.len() as int) =~= o0);
            assert(items_ok(t, ric as nat, bw as nat, its)) by {
                assert forall|k: int| 0 <= k < its.len() implies {
                    &&& item_ok(t, bw as nat, #[trigger] its[k])
                    &&& (iref(its[k]) matches Some(a) ==> a < ric)
                } by {
                    if !refs.has {
                        lemma_item_base(t, base as nat, bw as nat, its[k]);
                    }
                }
            }
            lemma_fsum(its);
            assert forall|ms: nat| ms >= fsizes(fields.view()) implies #[trigger] section(t, mc, ms, sb) == SecR::Ok(fields.view(), ric as nat) by {
                lemma_section_rt(t, mc, ms, ric as nat, bw as nat, its);
            }
        }
        if ric > 0 {
            let ghost sv0 = sview(self.sent@);
            self.sent.push(SentX { stream, ric, min_ref: refs.min });
            proof {
                assert(sview(self.sent@) =~= sv0.push(Sent { stream: stream as nat, ric: ric as nat, min_ref: refs.min as nat }));
            }
            if ric > self.krc && !self.contains_risky(stream) {
                let ghost rv0 = self.risky@;
                self.risky.push(stream);
                proof {
                    assert(nats(self.risky@) =~= nats(rv0).push(stream as nat));
                }
            }
            proof {
                let st = self.state();
                let ss = nats(self.risky@);
                assert forall|j: int| 0 <= j < st.sent.len() && #[trigger] st.sent[j].ric > st.krc implies ss.contains(st.sent[j].stream) by {
                    if j < sv0.len() {
                        assert(st.sent[j] == sv0[j]);
                        assert(covers(nats(old(self).risky@), sv0, st.krc));
                        let w = choose|w: int| 0 <= w < nats(old(self).risky@).len() && nats(old(self).risky@)[w] == sv0[j].stream;
                        assert(ss[w] == nats(old(self).risky@)[w]);
                    } else {
                        assert(st.sent[j].stream == stream as nat);
                        if nats(old(self).risky@).contains(stream as nat) {
                            let w = choose|w: int| 0 <= w < nats(old(self).risky@).len() && nats(old(self).risky@)[w] == stream as nat;
                            assert(ss[w] == nats(old(self).risky@)[w]);
                        } else {
                            assert(ss[ss.len() - 1] == stream as nat);
                        }
                    }
                }
                assert(covers(ss, st.sent, st.krc));
                assert forall|j: int| 0 <= j < st.sent.len() implies st.table.dropped <= #[trigger] st.sent[j].min_ref by {
                    if j < sv0.len() {
                        assert(st.sent[j] == sv0[j]);
                    }
                }
                assert forall|j: int| 0 <= j < st.sent.len() implies 0 < #[trigger] st.sent[j].ric <= icount(st.table) by {
                    if j < sv0.len() {
                        assert(st.sent[j] == sv0[j]);
                    }
                }
            }
        }
        Ghost(ric as nat)
    }

    fn contains_risky(&self, stream: u64) -> (r: bool)
        ensures
            r == nats(self.risky@).contains(stream as nat),
    {
        let mut i: usize = 0;
        while i < self.risky.len()
            invariant
                i <= self.risky@.len(),
                forall|j: int| 0 <= j < i ==> self.risky@[j] != stream,
            decreases self.risky@.len() - i,
        {
            if self.risky[i] == stream {
                proof {
                    assert(nats(self.risky@)[i as int] == stream as nat);
                }
                return true;
            }
            i = i + 1;
        }
        proof {
            if nats(self.risky@).contains(stream as nat) {
                let j = choose|j: int| 0 <= j < nats(self.risky@).len() && nats(self.risky@)[j] == stream as nat;
                assert(self.risky@[j] == stream);
            }
        }
        false
    }

    /// Everything but the unacknowledged sections and the Known Received
    /// Count is as in `o`.
    pub open spec fn same_but_acks(&self, o: &Encoder) -> bool {
        &&& self.table.view() == o.table.view()
        &&& self.table.inv() == o.table.inv()
        &&& self.max_cap == o.max_cap
        &&& self.max_blocked == o.max_blocked
        &&& self.es@ == o.es@
        &&& self.es_all@ == o.es_all@
        &&& self.taken@ == o.taken@
        &&& self.held@ == o.held@
    }

    /// Applies the decoder instruction `b` (all of it).
    fn dapply(&mut self, b: &[u8]) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            match dinst(old(self).state(), b@) {
                None => !r,
                Some(st) => r && final(self).state() == st && final(self).inv() && final(self).same_but_acks(old(self)),
            },
    {
        proof {
            reveal(dinst);
        }
        if b.len() == 0 {
            return false;
        }
        let ghost st0 = self.state();
        let ghost ss = nats(self.risky@);
        if b[0] >= 0x80 {
            match integer::decode(b, 0, 7) {
                IntE::Ok(s, _) => {
                    let mut i: usize = 0;
                    let mut found = false;
                    while i < self.sent.len() && !found
                        invariant
                            i <= self.sent@.len(),
                            found ==> i < self.sent@.len() && self.sent@[i as int].stream == s,
                            forall|j: int| 0 <= j < i ==> #[trigger] self.sent@[j].stream != s,
                        decreases self.sent@.len() - i + (if found { 0int } else { 1int }),
                    {
                        if self.sent[i].stream == s {
                            found = true;
                        } else {
                            i = i + 1;
                        }
                    }
                    if !found {
                        proof {
                            if exists|k: int| 0 <= k < st0.sent.len() && #[trigger] st0.sent[k].stream == s as nat {
                                let k = choose|k: int| 0 <= k < st0.sent.len() && #[trigger] st0.sent[k].stream == s as nat;
                                assert(self.sent@[k].stream != s);
                            }
                        }
                        return false;
                    }
                    proof {
                        assert forall|j: int| 0 <= j < i implies #[trigger] st0.sent[j].stream != s as nat by {
                            assert(self.sent@[j].stream != s);
                        }
                        lemma_first_of(st0.sent, s as nat, i as int);
                        lemma_remove_sub(st0.sent, i as int);
                    }
                    let ric = self.sent[i].ric;
                    let ghost sv = self.sent@;
                    self.sent.remove(i);
                    if ric > self.krc {
                        self.krc = ric;
                    }
                    proof {
                        assert(sview(self.sent@) =~= st0.sent.remove(i as int));
                        lemma_enc_ok_sub(st0, st0.sent.remove(i as int), self.krc as nat, ss);
                    }
                    true
                },
                _ => false,
            }
        } else if b[0] >= 0x40 {
            match integer::decode(b, 0, 6) {
                IntE::Ok(s, _) => {
                    let mut kept: Vec<SentX> = Vec::new();
                    let mut i: usize = 0;
                    proof {
                        assert(st0.sent.take(0).len() == 0);
                        assert(sview(kept@) =~= drop_stream(st0.sent.take(0), s as nat));
                    }
                    while i < self.sent.len()
                        invariant
                            i <= self.sent@.len(),
                            st0 == old(self).state(),
                            self.sent@ == old(self).sent@,
                            sview(kept@) == drop_stream(st0.sent.take(i as int), s as nat),
                        decreases self.sent@.len() - i,
                    {
                        let x = self.sent[i];
                        proof {
                            let p = st0.sent.take(i + 1);
                            assert(p.drop_last() =~= st0.sent.take(i as int));
                            assert(p.last() == sview(self.sent@)[i as int]);
                        }
                        if x.stream != s {
                            let ghost k0 = kept@;
                            kept.push(x);
                            proof {
                                assert(sview(kept@) =~= sview(k0).push(sview(self.sent@)[i as int]));
                            }
                        }
                        i = i + 1;
                    }
                    proof {
                        assert(st0.sent.take(i as int) =~= st0.sent);
                        lemma_drop_stream_sub(st0.sent, s as nat);
                        lemma_enc_ok_sub(st0, drop_stream(st0.sent, s as nat), self.krc as nat, ss);
                    }
                    self.sent = kept;
                    true
                },
                _ => false,
            }
        } else {
            match integer::decode(b, 0, 6) {
                IntE::Ok(n, _) => {
                    let ic = self.table.icount();
                    if n == 0 || n > ic - self.krc {
                        return false;
                    }
                    self.krc = self.krc + n;
                    proof {
                        assert(sub(st0.sent, st0.sent));
                        lemma_enc_ok_sub(st0, st0.sent, self.krc as nat, ss);
                    }
                    true
                },
                _ => false,
            }
        }
    }

    /// Runs the decoder stream `b` (`spec::drun`): the bytes consumed.
    fn drun_x(&mut self, b: &[u8]) -> (r: Option<usize>)
        requires
            old(self).inv(),
        ensures
            match drun(old(self).state(), b@) {
                Run::Bad => r is None,
                Run::Ok(st, k) => r == Some(k as usize) && final(self).state() == st && final(self).inv()
                    && final(self).same_but_acks(old(self)),
            },
    {
        let ghost st0 = self.state();
        let mut pos: usize = 0;
        proof {
            assert(b@.subrange(0, b@.len() as int) =~= b@);
        }
        loop
            invariant
                pos <= b@.len(),
                self.inv(),
                self.same_but_acks(old(self)),
                st0 == old(self).state(),
                drun(st0, b@) == shift(drun(self.state(), b@.subrange(pos as int, b@.len() as int)), pos as int),
            decreases b@.len() - pos,
        {
            let rest = vstd::slice::slice_subrange(b, pos, b.len());
            proof {
                assert(rest@ == b@.subrange(pos as int, b@.len() as int));
            }
            match dframe_x(rest) {
                EndE::Short => {
                    return Some(pos);
                },
                EndE::Bad => {
                    return None;
                },
                EndE::Ok(e) => {
                    let ins = vstd::slice::slice_subrange(rest, 0, e);
                    proof {
                        assert(ins@ == rest@.subrange(0, e as int));
                    }
                    if !self.dapply(ins) {
                        return None;
                    }
                    proof {
                        let r2 = rest@.subrange(e as int, rest@.len() as int);
                        assert(r2 =~= b@.subrange(pos + e, b@.len() as int));
                        match drun(self.state(), r2) {
                            Run::Bad => {},
                            Run::Ok(_, _) => {},
                        }
                    }
                    pos = pos + e;
                },
            }
        }
    }

    /// Reads the decoder stream: `input` is its next bytes, after `held`
    /// (`spec::drun`, from the bytes not yet consumed). By split invariance
    /// (`lemmas::lemma_drun_split`), however the stream is cut into
    /// pieces, the encoder ends in the same state. False is
    /// QPACK_DECODER_STREAM_ERROR.
    pub fn feed_decoder(&mut self, input: &[u8]) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            match drun(old(self).state(), old(self).held@ + input@) {
                Run::Bad => !ok,
                Run::Ok(st, k) => ok && final(self).inv() && final(self).state() == st
                    && final(self).held@ == (old(self).held@ + input@).subrange(k, (old(self).held@.len() + input@.len()) as int)
                    && final(self).es@ == old(self).es@ && final(self).es_all@ == old(self).es_all@
                    && final(self).taken@ == old(self).taken@,
            },
    {
        let ghost st0 = self.state();
        let ghost h0 = self.held@;
        let ghost all = h0 + input@;
        if self.held.len() == 0 {
            proof {
                assert(all =~= input@);
            }
            let k = match self.drun_x(input) {
                Some(k) => k,
                None => {
                    return false;
                },
            };
            proof {
                lemma_drun_rest(st0, input@);
            }
            let rest = vstd::slice::slice_subrange(input, k, input.len());
            extend(&mut self.held, rest);
            proof {
                assert(self.held@ =~= all.subrange(k as int, all.len() as int));
            }
        } else {
            let ghost hl = h0.len();
            let mut buf: Vec<u8> = Vec::new();
            core::mem::swap(&mut buf, &mut self.held);
            proof {
                reveal(dframe);
                assert(dframe(self.held@) is Short);
            }
            extend(&mut buf, input);
            proof {
                assert(buf@ =~= all);
            }
            let k = match self.drun_x(buf.as_slice()) {
                Some(k) => k,
                None => {
                    return false;
                },
            };
            proof {
                lemma_drun_rest(st0, all);
                lemma_drun_first(st0, all);
                assert(all.subrange(0, hl as int) =~= h0);
                lemma_dframe_short_prefix(all, hl as int);
            }
            self.held = to_vec(vstd::slice::slice_subrange(buf.as_slice(), k, buf.len()));
        }
        proof {
            assert(dframe(self.held@) is Short);
        }
        true
    }

    /// Whether stream `s` has a section that could block.
    fn has_risky(&self, s: u64) -> (r: bool)
        ensures
            r == exists|j: int| 0 <= j < self.sent@.len() && #[trigger] self.sent@[j].stream == s && self.sent@[j].ric > self.krc,
    {
        let mut i: usize = 0;
        while i < self.sent.len()
            invariant
                i <= self.sent@.len(),
                forall|j: int| 0 <= j < i ==> !(#[trigger] self.sent@[j].stream == s && self.sent@[j].ric > self.krc),
            decreases self.sent@.len() - i,
        {
            if self.sent[i].stream == s && self.sent[i].ric > self.krc {
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// Drops the streams that can no longer block from `risky`.
    fn prune_risky(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).state() == old(self).state(),
            final(self).same_but_acks(old(self)),
    {
        let mut kept: Vec<u64> = Vec::new();
        let mut i: usize = 0;
        let ghost sv = sview(self.sent@);
        let ghost ss = nats(self.risky@);
        while i < self.risky.len()
            invariant
                self.inv(),
                sv == sview(self.sent@),
                ss == nats(self.risky@),
                i <= self.risky@.len(),
                kept@.len() <= i,
                forall|j: int| 0 <= j < sv.len() && #[trigger] sv[j].ric > self.krc && ss.take(i as int).contains(sv[j].stream)
                    ==> nats(kept@).contains(sv[j].stream),
            decreases self.risky@.len() - i,
        {
            let s = self.risky[i];
            let h = self.has_risky(s);
            let ghost k0 = kept@;
            if h {
                kept.push(s);
            }
            proof {
                assert(nats(kept@) == if h { nats(k0).push(s as nat) } else { nats(k0) }) by {
                    if h {
                        assert(nats(kept@) =~= nats(k0).push(s as nat));
                    }
                }
                assert forall|j: int| 0 <= j < sv.len() && #[trigger] sv[j].ric > self.krc && ss.take(i + 1).contains(sv[j].stream)
                    implies nats(kept@).contains(sv[j].stream) by {
                    let w = choose|w: int| 0 <= w < i + 1 && #[trigger] ss.take(i + 1)[w] == sv[j].stream;
                    if w < i {
                        assert(ss.take(i as int)[w] == sv[j].stream);
                        assert(nats(k0).contains(sv[j].stream));
                        let z = choose|z: int| 0 <= z < nats(k0).len() && nats(k0)[z] == sv[j].stream;
                        assert(nats(kept@)[z] == nats(k0)[z]);
                    } else {
                        assert(sv[j].stream == s as nat);
                        assert(self.sent@[j].stream == s && self.sent@[j].ric > self.krc);
                        assert(h);
                        assert(nats(kept@)[nats(kept@).len() - 1] == s as nat);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(ss.take(i as int) =~= ss);
            assert(covers(nats(kept@), sv, self.krc as nat));
        }
        self.risky = kept;
    }
}

} // verus!
