//! The verified decoder: one field representation at a time (`rep`), and
//! the streaming wrapper that accepts input in arbitrary pieces (`feed`).
use crate::huffman;
use crate::lemmas::*;
use crate::integer::{self, IntE};
use crate::spec::*;
use crate::table::*;
use verilith_core::prims::extend;
use vstd::prelude::*;

verus! {

/// A decoder (one per HTTP/2 connection direction).
pub struct Decoder {
    /// The dynamic table.
    pub table: Table,
    /// The table size limit from SETTINGS_HEADER_TABLE_SIZE.
    pub settings: u32,
    /// The smallest limit set since the last size update (`NO_LIMIT` if none is pending), which the next update may not exceed.
    pub pending: u32,
    /// Whether no field has been decoded yet in this header block, where size updates are allowed.
    pub at_start: bool,
    /// Whether a size update must come first, after the limit was lowered.
    pub expect: bool,
    /// The last field's name and value.
    pub name: Vec<u8>,
    /// The last field's value (see `value_ref`).
    pub value: Vec<u8>,
    /// Input of a representation that has not fully arrived (`feed`).
    pub buf: Vec<u8>,
    /// How long `buf` must be before decoding it is worth trying again.
    pub need: usize,
    /// If not 0, the last field's name is that of table entry `name_ref`
    /// (index space of §2.3.3), not `name` (see `name_v`).
    pub name_ref: usize,
    /// The same for the value.
    pub value_ref: usize,
    /// The Huffman decoding table (`huffman::dtab_ok`).
    pub dt: &'static [u32],
    /// If not 0, `name` holds the name string of the representation in
    /// `buf`, already decoded, which ends at `buf[name_end]`: decoding
    /// `buf` again when more input comes starts after it (`held_ok`).
    pub name_end: usize,
}

/// `feed` buffers at most this much of an unfinished representation (one
/// is at most 131085 bytes: two 65536-byte strings and their lengths).
pub const MAX_BUF: usize = 0x100_0000;

/// What `feed` found.
#[derive(Clone, Copy)]
pub enum Feed {
    /// All input is consumed; the block is not over.
    More,
    /// All input is consumed and, with `fin`, the block ended cleanly.
    Final,
    /// A field (in `name` and `value`, never-indexed or not), after this
    /// many bytes of input.
    Field(usize, bool),
    /// A decoding error (or more than `MAX_BUF` bytes of one
    /// representation).
    Bad,
}

/// One step's result.
pub enum Step {
    /// The input ends inside the representation; at least this many bytes
    /// are needed before it can be decoded. The second number is where
    /// the representation's name string ends if it was decoded into
    /// `name` (a new name), or 0.
    Short(usize, usize),
    /// A decoding error.
    Bad,
    /// A field (in `name` and `value`), whether it is never-indexed, and
    /// the representation's length.
    Field(usize, bool),
    /// A dynamic table size update and its length.
    Update(usize),
}

/// What reading a string literal found.
pub enum StrE {
    /// The input ends inside it; at least this many bytes are needed.
    Short(usize),
    /// A decoding error.
    Bad,
    /// The string was read; it ends at this position.
    Ok(usize),
}

/// Reads the string literal at `b[pos]` into `out`. The second result is
/// its work: the Huffman decoder's (`huffman::decode_metered`), or the bytes
/// copied.
pub fn read_str(b: &[u8], pos: usize, out: &mut Vec<u8>, t: &[u32]) -> (r: (StrE, Ghost<nat>))
    requires
        huffman::layout_ok(),
        huffman::dtab_ok(t@),
        b@.len() + 0x2_0000 < usize::MAX,
    ensures
        match (r.0, str_dec(b@, pos as int)) {
            (StrE::Short(need), StrR::Short) => need > b@.len() && str_short_upto(b@, pos as int, need as int),
            (StrE::Bad, StrR::Bad) => true,
            (StrE::Ok(e), StrR::Ok(s, se)) => e as int == se && final(out)@ == s && e <= b@.len(),
            _ => false,
        },
        final(out)@.len() <= 8 * MAX_STR,
        r.0 is Short ==> r.1@ == 0,
        r.0 matches StrE::Ok(e) ==> pos < e && r.1@ <= 4 * (e - pos) + 4,
        r.1@ <= 4 * b@.len() + 4,
{
    match integer::decode(b, pos, 7) {
        IntE::Short => {
            out.clear();
            proof {
                lemma_str_short_same(b@, pos as int);
            }
            (StrE::Short(b.len() + 1), Ghost(0))
        },
        IntE::Bad => {
            out.clear();
            (StrE::Bad, Ghost(0))
        },
        IntE::Ok(n, e) => {
            proof {
                crate::lemmas::lemma_int_ext(b@, Seq::empty(), pos as int, 7);
            }
            if n > MAX_STR {
                out.clear();
                return (StrE::Bad, Ghost(0));
            }
            if n as usize > b.len() - e {
                out.clear();
                proof {
                    assert forall|b2: Seq<u8>| ext_of(b2, b@) && b2.len() < e + n implies #[trigger] str_dec(b2, pos as int) is Short by {
                        lemma_ext_split(b2, b@);
                        crate::lemmas::lemma_int_ext(b@, b2.subrange(b@.len() as int, b2.len() as int), pos as int, 7);
                    }
                }
                return (StrE::Short(e + n as usize), Ghost(0));
            }
            let raw = vstd::slice::slice_subrange(b, e, e + n as usize);
            proof {
                assert(raw@ == b@.subrange(e as int, e + n));
            }
            if b[pos] >= 128 {
                let (ok, g) = huffman::decode_metered(raw, out, t);
                if ok {
                    (StrE::Ok(e + n as usize), g)
                } else {
                    (StrE::Bad, g)
                }
            } else {
                out.clear();
                extend(out, raw);
                proof {
                    assert(out@ =~= raw@);
                }
                (StrE::Ok(e + n as usize), Ghost(n as nat))
            }
        },
    }
}

/// Copies `s` into `out`.
fn set(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == s@,
{
    out.clear();
    extend(out, s);
    proof {
        assert(final(out)@ =~= s@);
    }
}

/// A copy of `v`.
fn copy(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    let mut r = Vec::with_capacity(v.len());
    extend(&mut r, v.as_slice());
    proof {
        assert(r@ =~= v@);
    }
    r
}

impl Decoder {
    pub open spec fn state(&self) -> DState {
        DState {
            table: self.table.view(),
            max: self.table.max as nat,
            settings: self.settings as nat,
            pending: self.pending as nat,
            at_start: self.at_start,
            expect: self.expect,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.table.inv()
        &&& huffman::layout_ok()
        &&& huffman::dtab_ok(self.dt@)
        &&& self.name_ref <= self.table.view().len() + 61
        &&& self.value_ref <= self.table.view().len() + 61
        &&& self.table.max <= self.settings
    }

    /// What `feed` keeps between calls: a buffered representation is too
    /// short to decode with anything less than `need` bytes, and a name
    /// cached for it (`name_end`) is its decoded name string.
    pub open spec fn held_ok(&self) -> bool {
        &&& self.buf@.len() > 0 ==> self.need > self.buf@.len() && short_upto(self.state(), self.buf@, self.need as int)
        &&& self.name_end <= self.buf@.len()
        &&& self.name_end > 0 ==> newname_byte(self.buf@[0]) && str_dec(self.buf@, 1) == StrR::Ok(self.name@, self.name_end as int)
            && self.name@.len() <= 8 * MAX_STR
    }

    /// The potential of the work bound (`feed_metered`): 8 steps for each
    /// buffered byte, less 4 for each byte of a cached name, and 1 for each
    /// dynamic table entry, which pays for its eviction. It is never
    /// negative (`held_ok`).
    pub open spec fn pot(&self) -> int {
        8 * self.buf@.len() + self.table.view().len() - 4 * self.name_end
    }

    /// The last field's name.
    pub open spec fn name_v(&self) -> Seq<u8> {
        if self.name_ref == 0 {
            self.name@
        } else {
            entry(self.table.view(), self.name_ref as nat).0
        }
    }

    /// The last field's value.
    pub open spec fn value_v(&self) -> Seq<u8> {
        if self.value_ref == 0 {
            self.value@
        } else {
            entry(self.table.view(), self.value_ref as nat).1
        }
    }

    /// The last field's name.
    pub fn name(&self) -> (r: &[u8])
        requires
            self.inv(),
        ensures
            r@ == self.name_v(),
    {
        if self.name_ref == 0 {
            self.name.as_slice()
        } else {
            self.table.get(self.name_ref).0
        }
    }

    /// The last field's value.
    pub fn value(&self) -> (r: &[u8])
        requires
            self.inv(),
        ensures
            r@ == self.value_v(),
    {
        if self.value_ref == 0 {
            self.value.as_slice()
        } else {
            self.table.get(self.value_ref).1
        }
    }

    /// A decoder in the initial state, or `None` if the Huffman layout
    /// check fails (it does not: see tests/tables.rs).
    pub fn new() -> (r: Option<Decoder>)
        ensures
            r matches Some(d) ==> d.inv() && d.held_ok() && d.state() == initial() && d.buf@.len() == 0 && d.pot() == 0,
    {
        let dt = match huffman::dtab() {
            Some(t) => t,
            None => return None,
        };
        let d = Decoder {
            table: Table::new(4096),
            settings: 4096,
            pending: NO_LIMIT,
            at_start: true,
            expect: false,
            name: Vec::new(),
            value: Vec::new(),
            buf: Vec::new(),
            need: 0,
            dt,
            name_ref: 0,
            value_ref: 0,
            name_end: 0,
        };
        proof {
            assert(d.state().table =~= initial().table);
        }
        Some(d)
    }

    /// Decodes the representation at the start of `b` (`spec::rep`). The
    /// state changes only on a field or a size update.
    #[inline(always)]
    pub fn rep(&mut self, b: &[u8]) -> (r: Step)
        requires
            old(self).inv(),
            b@.len() + 0x2_0000 < usize::MAX,
        ensures
            final(self).inv(),
            final(self).buf == old(self).buf,
            match (r, rep(old(self).state(), b@)) {
                (Step::Short(need, _), Rep::Short) => need > b@.len() && final(self).state() == old(self).state(),
                (Step::Bad, Rep::Bad) => final(self).state() == old(self).state(),
                (Step::Field(e, never), Rep::Field(f, st, se)) => {
                    &&& e as int == se
                    &&& e <= b@.len()
                    &&& final(self).name_v() == f.name
                    &&& final(self).value_v() == f.value
                    &&& never == f.never
                    &&& final(self).state() == st
                },
                (Step::Update(e), Rep::Update(st, se)) => e as int == se && e <= b@.len() && final(self).state() == st,
                _ => false,
            },
    {
        self.rep_from(b, 0).0
    }

    /// `rep`, given with `skip` (if not 0) that `name` already holds the
    /// name string of `b`, which ends at `b[skip]`; and its work. On
    /// `Short`, it says how far input that starts with `b` must reach
    /// before decoding it again is worth it (`short_upto`), and whether
    /// `name` then holds the name string.
    ///
    /// Work counts the Huffman decoder's turns, bytes copied, and table
    /// evictions; the integer decoder takes at most 6 turns and is not
    /// counted. Decoding `e` bytes costs at most `4e + 5`, plus a copy of
    /// at most `settings + 64` bytes for a field that adds an indexed name
    /// to the table, plus 1 per entry evicted, paid for by the entry.
    #[verifier::rlimit(80)]
    #[inline(always)]
    pub fn rep_from(&mut self, b: &[u8], skip: usize) -> (r: (Step, Ghost<nat>))
        requires
            old(self).inv(),
            b@.len() + 0x2_0000 < usize::MAX,
            skip > 0 ==> skip <= b@.len() && newname_byte(b@[0]) && str_dec(b@, 1) == StrR::Ok(old(self).name@, skip as int)
            && old(self).name@.len() <= 8 * MAX_STR,
        ensures
            final(self).inv(),
            final(self).buf == old(self).buf,
            final(self).need == old(self).need,
            final(self).name_end == old(self).name_end,
            final(self).settings == old(self).settings,
            match (r.0, rep(old(self).state(), b@)) {
                (Step::Short(need, ne), Rep::Short) => {
                    &&& need > b@.len()
                    &&& short_upto(old(self).state(), b@, need as int)
                    &&& final(self).state() == old(self).state()
                    &&& ne <= b@.len()
                    &&& (ne > 0 ==> newname_byte(b@[0]) && str_dec(b@, 1) == StrR::Ok(final(self).name@, ne as int)
                        && final(self).name@.len() <= 8 * MAX_STR)
                    &&& (skip > 0 ==> ne == skip)
                    &&& r.1@ + 4 * skip <= 4 * ne + 4
                },
                (Step::Bad, Rep::Bad) => final(self).state() == old(self).state() && r.1@ + 4 * skip <= 8 * b@.len() + 8,
                (Step::Field(e, never), Rep::Field(f, st, se)) => {
                    &&& e as int == se
                    &&& e <= b@.len()
                    &&& final(self).name_v() == f.name
                    &&& final(self).value_v() == f.value
                    &&& never == f.never
                    &&& final(self).state() == st
                    &&& r.1@ + final(self).table.view().len() + 4 * skip <= old(self).table.view().len() + 4 * e + 5 + old(self).settings + 64
                },
                (Step::Update(e), Rep::Update(st, se)) => {
                    &&& e as int == se
                    &&& e <= b@.len()
                    &&& final(self).state() == st
                    &&& r.1@ + final(self).table.view().len() <= old(self).table.view().len()
                },
                _ => false,
            },
    {
        let ghost st0 = self.state();
        self.name_ref = 0;
        self.value_ref = 0;
        if b.len() == 0 {
            proof {
                lemma_short_same(st0, b@);
            }
            return (Step::Short(1, 0), Ghost(0));
        }
        let c = b[0];
        if c & 0xE0 == 0x20 {
            if !self.at_start {
                return (Step::Bad, Ghost(0));
            }
            match integer::decode(b, 0, 5) {
                IntE::Short => {
                    proof {
                        lemma_short_same(st0, b@);
                    }
                    (Step::Short(b.len() + 1, 0), Ghost(0))
                },
                IntE::Bad => (Step::Bad, Ghost(0)),
                IntE::Ok(v, e) => {
                    let lim = if self.pending < self.settings { self.pending } else { self.settings };
                    if v > lim {
                        return (Step::Bad, Ghost(0));
                    }
                    let g = self.table.resize(v);
                    self.pending = NO_LIMIT;
                    self.expect = false;
                    (Step::Update(e), g)
                },
            }
        } else if self.expect {
            (Step::Bad, Ghost(0))
        } else if c >= 0x80 {
            match integer::decode(b, 0, 7) {
                IntE::Short => {
                    proof {
                        lemma_short_same(st0, b@);
                    }
                    (Step::Short(b.len() + 1, 0), Ghost(0))
                },
                IntE::Bad => (Step::Bad, Ghost(0)),
                IntE::Ok(i, e) => {
                    if i == 0 || i as usize > self.table.len() + 61 {
                        return (Step::Bad, Ghost(0));
                    }
                    // The field is the entry: no copy.
                    self.name_ref = i as usize;
                    self.value_ref = i as usize;
                    self.at_start = false;
                    (Step::Field(e, false), Ghost(0))
                },
            }
        } else {
            let incr = c & 0x40 != 0;
            let never = c & 0xF0 == 0x10;
            let newname = c == 0x40 || c == 0x00 || c == 0x10;
            let ghost mut cost: nat = 0;
            let mut ne: usize = 0;
            // An indexed name to copy once the value has been read.
            let mut idx: usize = 0;
            let e1 = if newname {
                if skip > 0 {
                    ne = skip;
                    skip
                } else {
                    match read_str(b, 1, &mut self.name, self.dt) {
                        (StrE::Short(need), _) => {
                            proof {
                                assert forall|b2: Seq<u8>| ext_of(b2, b@) && b2.len() < need implies #[trigger] rep(st0, b2) is Short by {
                                    lemma_ext_split(b2, b@);
                                    assert(str_dec(b2, 1) is Short);
                                }
                            }
                            return (Step::Short(need, 0), Ghost(0));
                        },
                        (StrE::Bad, g) => return (Step::Bad, g),
                        (StrE::Ok(e), g) => {
                            proof {
                                cost = g@;
                            }
                            ne = e;
                            e
                        },
                    }
                }
            } else {
                match integer::decode(b, 0, if incr { 6 } else { 4 }) {
                    IntE::Short => {
                        proof {
                            lemma_short_same(st0, b@);
                        }
                        return (Step::Short(b.len() + 1, 0), Ghost(0));
                    },
                    IntE::Bad => return (Step::Bad, Ghost(0)),
                    IntE::Ok(i, e) => {
                        if i == 0 || i as usize > self.table.len() + 61 {
                            return (Step::Bad, Ghost(0));
                        }
                        if incr {
                            idx = i as usize;
                        } else {
                            self.name_ref = i as usize;
                        }
                        e
                    },
                }
            };
            proof {
                if newname {
                    crate::lemmas::lemma_str_ext(b@, Seq::empty(), 1);
                } else {
                    crate::lemmas::lemma_int_ext(b@, Seq::empty(), 0, if incr { 6 } else { 4 });
                }
            }
            let e2 = match read_str(b, e1, &mut self.value, self.dt) {
                (StrE::Short(need), g) => {
                    proof {
                        assert forall|b2: Seq<u8>| ext_of(b2, b@) && b2.len() < need implies #[trigger] rep(st0, b2) is Short by {
                            lemma_ext_split(b2, b@);
                            let c2 = b2.subrange(b@.len() as int, b2.len() as int);
                            if newname {
                                crate::lemmas::lemma_str_ext(b@, c2, 1);
                            } else {
                                crate::lemmas::lemma_int_ext(b@, c2, 0, if incr { 6 } else { 4 });
                            }
                            assert(str_dec(b2, e1 as int) is Short);
                        }
                    }
                    return (Step::Short(need, ne), Ghost(cost + g@));
                },
                (StrE::Bad, g) => return (Step::Bad, Ghost(cost + g@)),
                (StrE::Ok(e), g) => {
                    proof {
                        cost = cost + g@;
                    }
                    e
                },
            };
            if idx > 0 {
                let (n, _) = self.table.get(idx);
                proof {
                    cost = cost + n@.len();
                }
                set(&mut self.name, n);
            }
            if incr {
                // The buffers move into the table: the field is then its
                // newest entry.
                let (ok, g) = self.table.insert_move(&mut self.name, &mut self.value);
                proof {
                    cost = cost + g@;
                }
                if ok {
                    self.name_ref = 62;
                    self.value_ref = 62;
                }
            }
            self.at_start = false;
            (Step::Field(e2, never), Ghost(cost))
        }
    }
}

/// The first byte of a literal with a new name (§6.2).
pub open spec fn newname_byte(c: u8) -> bool {
    c == 0x40 || c == 0x00 || c == 0x10
}

/// A copy of `s[a..]`.
fn tail(s: &[u8], a: usize) -> (r: Vec<u8>)
    requires
        a <= s@.len(),
    ensures
        r@ == s@.subrange(a as int, s@.len() as int),
{
    let mut r = Vec::new();
    extend(&mut r, vstd::slice::slice_subrange(s, a, s.len()));
    r
}

/// `feed`'s result, as the spec relates it to the decoder `d` after the
/// call: `s` is the undecoded input (buffer, then `input`), `st0` the state
/// at its start, `ob` the old buffer's length.
pub open spec fn feed_ok(st0: DState, s: Seq<u8>, ob: int, n: int, fin: bool, r: Feed, d: Decoder) -> bool {
    match r {
        Feed::Field(c, never) => exists|k: int| 0 <= k && match #[trigger] upd(st0, s, k) {
            Some(s1) => match rep(s1, s.subrange(k, s.len() as int)) {
                Rep::Field(f, st, e) => {
                    &&& st == d.state()
                    &&& k + e <= ob + c
                    &&& c <= n
                    &&& d.buf@ == s.subrange(k + e, ob + c)
                    &&& d.name_v() == f.name
                    &&& d.value_v() == f.value
                    &&& never == f.never
                },
                _ => false,
            },
            None => false,
        },
        Feed::More => exists|k: int| {
            &&& 0 <= k <= s.len()
            &&& #[trigger] upd(st0, s, k) == Some(d.state())
            &&& d.buf@ == s.subrange(k, s.len() as int)
        },
        Feed::Final => {
            &&& fin
            &&& upd(st0, s, s.len() as int) == Some(d.state())
            &&& !d.state().expect
            &&& d.buf@.len() == 0
        },
        Feed::Bad => exists|k: int| 0 <= k <= s.len() && match #[trigger] upd(st0, s, k) {
            Some(s1) => {
                let rest = s.subrange(k, s.len() as int);
                ||| rep(s1, rest) is Bad
                ||| (fin && rest.len() > 0 && rep(s1, rest) is Short)
                ||| (fin && rest.len() == 0 && s1.expect)
                ||| rest.len() > MAX_BUF
            },
            None => false,
        },
    }
}

/// `feed`'s loop invariant: the state is `st0` after `k` bytes of size
/// updates, and the buffer holds the input from there to `pos`.
pub open spec fn feed_inv(st0: DState, s: Seq<u8>, ob: int, n: int, k: int, pos: int, d: Decoder) -> bool {
    &&& d.inv()
    &&& d.held_ok()
    &&& 0 <= pos <= n
    &&& s.len() == ob + n
    &&& 0 <= k <= ob + pos
    &&& upd(st0, s, k) == Some(d.state())
    &&& d.buf@ == s.subrange(k, ob + pos)
    &&& d.buf@.len() <= MAX_BUF + n
    &&& n < 0x1000_0000
}

/// What one step of `feed` decided.
pub enum Next {
    /// Stop, with this result.
    Done(Feed),
    /// Go on from this position.
    Go(usize),
}

impl Decoder {
    /// One round of `feed` with input buffered: completes the buffer from
    /// `input[pos..]` as far as `need`, then decodes it. A representation
    /// completed this way ends exactly at the end of the buffer
    /// (`lemmas::lemma_end_at_need`), so the buffer is then empty.
    #[verifier::rlimit(400)]
    fn feed_buffered(&mut self, input: &[u8], pos: usize, fin: bool, Ghost(st0): Ghost<DState>, Ghost(s): Ghost<Seq<u8>>, Ghost(ob): Ghost<int>, Ghost(k): Ghost<int>) -> (r: (Next, Ghost<int>, Ghost<nat>))
        requires
            feed_inv(st0, s, ob, input@.len() as int, k, pos as int, *old(self)),
            s == s.subrange(0, ob) + input@,
            old(self).buf@.len() > 0,
            old(self).buf@.len() <= MAX_BUF,
        ensures
            final(self).settings == old(self).settings,
            match r.0 {
                Next::Done(f) => {
                    &&& feed_ok(st0, s, ob, input@.len() as int, fin, f, *final(self))
                    &&& final(self).inv()
                    &&& final(self).held_ok()
                    &&& final(self).buf@.len() <= MAX_BUF + input@.len()
                    &&& r.2@ + final(self).pot() <= old(self).pot() + 15 * (input@.len() - pos) + 80 + old(self).settings
                },
                Next::Go(p2) => {
                    &&& feed_inv(st0, s, ob, input@.len() as int, r.1@, p2 as int, *final(self))
                    &&& (s.len() - r.1@) + (input@.len() - p2) < (s.len() - k) + (input@.len() - pos)
                    &&& p2 > pos
                    &&& r.2@ + final(self).pot() <= old(self).pot() + 15 * (p2 - pos)
                },
            },
    {
        let mut pos = pos;
        let pos0 = pos;
        let avail = input.len() - pos;
        let ghost b0 = self.buf@;
        proof {
            assert(input@ =~= s.subrange(ob, s.len() as int));
        }
        if !fin && self.buf.len() + avail < self.need {
            let more = vstd::slice::slice_subrange(input, pos, input.len());
            extend(&mut self.buf, more);
            proof {
                assert(self.buf@ =~= s.subrange(k, s.len() as int));
                lemma_short_more(self.state(), b0, more@, self.need as int);
                if self.name_end > 0 {
                    crate::lemmas::lemma_str_ext(b0, more@, 1);
                    assert(self.buf@[0] == b0[0]);
                }
            }
            return (Next::Done(Feed::More), Ghost(k), Ghost(avail as nat));
        }
        let take = if avail < self.need - self.buf.len() {
            avail
        } else {
            self.need - self.buf.len()
        };
        let taken = vstd::slice::slice_subrange(input, pos, pos + take);
        extend(&mut self.buf, taken);
        pos = pos + take;
        proof {
            assert(self.buf@ =~= s.subrange(k, ob + pos));
        }
        let mut bb: Vec<u8> = Vec::new();
        core::mem::swap(&mut bb, &mut self.buf);
        let skip = self.name_end;
        self.name_end = 0;
        let ghost s1 = self.state();
        let ghost rest = s.subrange(k, s.len() as int);
        let ghost more = s.subrange(ob + pos, s.len() as int);
        proof {
            assert(rest =~= bb@ + more);
            assert(bb@ == b0 + taken@);
            assert(ext_of(bb@, b0)) by {
                assert(bb@.subrange(0, b0.len() as int) =~= b0);
            }
            if skip > 0 {
                crate::lemmas::lemma_str_ext(b0, taken@, 1);
                assert(bb@[0] == b0[0]);
            }
        }
        let (st, g) = self.rep_from(bb.as_slice(), skip);
        match st {
            Step::Short(need, ne) => {
                self.need = need;
                self.buf = bb;
                self.name_end = ne;
                if pos == input.len() {
                    proof {
                        assert(rest =~= bb@);
                    }
                    if fin {
                        self.buf.clear();
                        self.name_end = 0;
                        return (Next::Done(Feed::Bad), Ghost(k), Ghost(take as nat + g@));
                    }
                    return (Next::Done(Feed::More), Ghost(k), Ghost(take as nat + g@));
                }
                (Next::Go(pos), Ghost(k), Ghost(take as nat + g@))
            },
            Step::Bad => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, bb@, more);
                }
                (Next::Done(Feed::Bad), Ghost(k), Ghost(take as nat + g@))
            },
            Step::Update(e) => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, bb@, more);
                    lemma_end_at_need(s1, b0, old(self).need as int, bb@);
                    lemma_taken(s1, b0, old(self).need as int, bb@);
                    crate::lemmas::lemma_upd_step(st0, s, k, s1, self.state(), e as int);
                }
                self.need = 0;
                let ghost k2 = k + e;
                proof {
                    assert(self.buf@ =~= s.subrange(k2, ob + pos));
                }
                (Next::Go(pos), Ghost(k2), Ghost(take as nat + g@))
            },
            Step::Field(e, never) => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, bb@, more);
                    lemma_end_at_need(s1, b0, old(self).need as int, bb@);
                    lemma_taken(s1, b0, old(self).need as int, bb@);
                }
                self.need = 0;
                proof {
                    assert(self.buf@ =~= s.subrange(k + e, ob + pos));
                    assert(upd(st0, s, k) == Some(s1));
                }
                (Next::Done(Feed::Field(pos, never)), Ghost(k), Ghost(take as nat + g@))
            },
        }
    }

    /// One round of `feed` with nothing buffered: decodes `input[pos..]`.
    #[verifier::rlimit(80)]
    #[inline(always)]
    fn feed_direct(&mut self, input: &[u8], pos: usize, fin: bool, Ghost(st0): Ghost<DState>, Ghost(s): Ghost<Seq<u8>>, Ghost(ob): Ghost<int>, Ghost(k): Ghost<int>) -> (r: (Next, Ghost<int>, Ghost<nat>))
        requires
            feed_inv(st0, s, ob, input@.len() as int, k, pos as int, *old(self)),
            s == s.subrange(0, ob) + input@,
            old(self).buf@.len() == 0,
        ensures
            final(self).settings == old(self).settings,
            match r.0 {
                Next::Done(f) => {
                    &&& feed_ok(st0, s, ob, input@.len() as int, fin, f, *final(self))
                    &&& final(self).inv()
                    &&& final(self).held_ok()
                    &&& final(self).buf@.len() <= MAX_BUF + input@.len()
                    &&& r.2@ + final(self).pot() <= old(self).pot() + 15 * (input@.len() - pos) + 80 + old(self).settings
                },
                Next::Go(p2) => {
                    &&& feed_inv(st0, s, ob, input@.len() as int, r.1@, p2 as int, *final(self))
                    &&& (s.len() - r.1@) + (input@.len() - p2) < (s.len() - k) + (input@.len() - pos)
                    &&& p2 > pos
                    &&& r.2@ + final(self).pot() <= old(self).pot() + 15 * (p2 - pos)
                },
            },
    {
        proof {
            assert(input@ =~= s.subrange(ob, s.len() as int));
            assert(k == ob + pos);
        }
        if pos == input.len() {
            proof {
                assert(s.subrange(k, s.len() as int).len() == 0);
            }
            if fin {
                if self.expect {
                    return (Next::Done(Feed::Bad), Ghost(k), Ghost(0));
                }
                return (Next::Done(Feed::Final), Ghost(k), Ghost(0));
            }
            proof {
                assert(self.buf@ =~= s.subrange(k, s.len() as int));
            }
            return (Next::Done(Feed::More), Ghost(k), Ghost(0));
        }
        let rest = vstd::slice::slice_subrange(input, pos, input.len());
        proof {
            assert(rest@ =~= s.subrange(k, s.len() as int));
        }
        let ghost s1 = self.state();
        let (st, g) = self.rep_from(rest, 0);
        match st {
            Step::Short(need, ne) => {
                if fin {
                    return (Next::Done(Feed::Bad), Ghost(k), g);
                }
                self.buf = tail(input, pos);
                self.need = need;
                self.name_end = ne;
                (Next::Done(Feed::More), Ghost(k), Ghost(rest@.len() + g@))
            },
            Step::Bad => (Next::Done(Feed::Bad), Ghost(k), g),
            Step::Update(e) => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, rest@, Seq::empty());
                    assert(rest@ + Seq::<u8>::empty() =~= rest@);
                    crate::lemmas::lemma_upd_step(st0, s, k, s1, self.state(), e as int);
                }
                let p2 = pos + e;
                proof {
                    assert(self.buf@ =~= s.subrange(k + e, ob + p2));
                }
                (Next::Go(p2), Ghost(k + e), g)
            },
            Step::Field(e, never) => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, rest@, Seq::empty());
                }
                let p2 = pos + e;
                proof {
                    assert(self.buf@ =~= s.subrange(k + e, ob + p2));
                    assert(upd(st0, s, k) == Some(s1));
                }
                (Next::Done(Feed::Field(p2, never)), Ghost(k), g)
            },
        }
    }

    /// Decodes input, in whatever pieces it arrives, up to the next header
    /// field (nghttp2's `nghttp2_hd_inflate_hd_nv`). Dynamic table size
    /// updates are applied on the way. `fin` says the header block ends
    /// with this input.
    ///
    /// With `S` the not-yet-decoded input (`buf`, then `input`) and the
    /// state at its start, the result is what decoding `S` as a whole
    /// gives (`feed_ok`): `upd` for the size updates, then `rep` for the
    /// next representation, each decoded from all of the rest of `S`.
    /// Since decoding a representation never depends on what follows it
    /// (`lemmas::lemma_rep_ext`), the fields are the same however the
    /// block is split into calls.
    #[inline(always)]
    pub fn feed(&mut self, input: &[u8], fin: bool) -> (r: Feed)
        requires
            old(self).inv(),
            old(self).held_ok(),
            input@.len() < 0x1000_0000,
            old(self).buf@.len() <= 0x2000_0000,
        ensures
            final(self).inv(),
            final(self).held_ok(),
            final(self).buf@.len() <= MAX_BUF + input@.len(),
            feed_ok(old(self).state(), old(self).buf@ + input@, old(self).buf@.len() as int, input@.len() as int, fin, r, *final(self)),
    {
        self.feed_metered(input, fin).0
    }

    /// `feed`, and its work, as a potential argument: the steps it takes
    /// plus the potential it leaves (`pot`) are at most the potential it
    /// found plus `16 * input.len() + 96 + settings`. The potential starts
    /// at 0 and is never negative, so over any sequence of calls the steps
    /// are at most `16` per input byte plus `96 + settings` per call. A
    /// step is a turn of a loop whose number of turns is not bounded by a
    /// constant (`feed`'s own, the Huffman decoder's, the table's
    /// eviction), or a byte copied.
    ///
    /// `settings` (SETTINGS_HEADER_TABLE_SIZE, 4096 unless the local side
    /// raises it) pays for the one copy that is not proportional to the
    /// input: a field that adds an indexed name to the table copies that
    /// name, which can be as long as an entry.
    #[verifier::rlimit(40)]
    #[inline(always)]
    pub fn feed_metered(&mut self, input: &[u8], fin: bool) -> (r: (Feed, Ghost<nat>))
        requires
            old(self).inv(),
            old(self).held_ok(),
            input@.len() < 0x1000_0000,
            old(self).buf@.len() <= 0x2000_0000,
        ensures
            final(self).inv(),
            final(self).held_ok(),
            final(self).buf@.len() <= MAX_BUF + input@.len(),
            feed_ok(old(self).state(), old(self).buf@ + input@, old(self).buf@.len() as int, input@.len() as int, fin, r.0, *final(self)),
            final(self).settings == old(self).settings,
            r.1@ + final(self).pot() <= old(self).pot() + 16 * input@.len() + 96 + old(self).settings,
    {
        let ghost st0 = self.state();
        let ghost s = self.buf@ + input@;
        let ghost ob = self.buf@.len() as int;
        if self.buf.len() > MAX_BUF {
            self.buf.clear();
            self.name_end = 0;
            proof {
                assert(upd(st0, s, 0) == Some(st0));
                assert(s.subrange(0, s.len() as int).len() > MAX_BUF);
            }
            return (Feed::Bad, Ghost(0));
        }
        let ghost mut k: int = 0;
        let ghost mut steps: nat = 0;
        let mut pos: usize = 0;
        proof {
            assert(self.buf@ =~= s.subrange(0, ob));
            assert(s.subrange(0, ob) + input@ =~= s);
        }
        loop
            invariant
                feed_inv(st0, s, ob, input@.len() as int, k, pos as int, *self),
                s == s.subrange(0, ob) + input@,
                s == old(self).buf@ + input@,
                ob == old(self).buf@.len(),
                st0 == old(self).state(),
                self.settings == old(self).settings,
                steps + self.pot() <= old(self).pot() + 16 * pos,
            decreases (s.len() - k) + (input@.len() - pos),
        {
            let r = if self.buf.len() > 0 {
                if self.buf.len() > MAX_BUF {
                    self.buf.clear();
                    self.name_end = 0;
                    proof {
                        assert(s.subrange(k, s.len() as int).len() > MAX_BUF);
                    }
                    return (Feed::Bad, Ghost(steps + 1));
                }
                self.feed_buffered(input, pos, fin, Ghost(st0), Ghost(s), Ghost(ob), Ghost(k))
            } else {
                self.feed_direct(input, pos, fin, Ghost(st0), Ghost(s), Ghost(ob), Ghost(k))
            };
            proof {
                steps = steps + 1 + r.2@;
            }
            match r.0 {
                Next::Done(f) => return (f, Ghost(steps)),
                Next::Go(p2) => {
                    pos = p2;
                    proof {
                        k = r.1@;
                    }
                },
            }
        }
    }

    /// SETTINGS_HEADER_TABLE_SIZE changed (`nghttp2_hd_inflate_change_table_size`).
    /// Allowed only between representations at the start of a block;
    /// returns false (nghttp2's NGHTTP2_ERR_INVALID_STATE) otherwise.
    pub fn change_settings(&mut self, n: u32) -> (ok: bool)
        requires
            old(self).inv(),
            old(self).held_ok(),
        ensures
            final(self).inv(),
            final(self).held_ok(),
            final(self).buf == old(self).buf,
            ok == (old(self).at_start && old(self).buf@.len() == 0),
            ok ==> final(self).state() == change_settings(old(self).state(), n as nat),
            !ok ==> final(self).state() == old(self).state(),
    {
        self.change_settings_metered(n).0
    }

    /// `change_settings`, and its work: one step per entry evicted, paid
    /// for by the entries (`pot`).
    pub fn change_settings_metered(&mut self, n: u32) -> (r: (bool, Ghost<nat>))
        requires
            old(self).inv(),
            old(self).held_ok(),
        ensures
            final(self).inv(),
            final(self).held_ok(),
            final(self).buf == old(self).buf,
            r.0 == (old(self).at_start && old(self).buf@.len() == 0),
            r.0 ==> final(self).state() == change_settings(old(self).state(), n as nat),
            !r.0 ==> final(self).state() == old(self).state(),
            r.1@ + final(self).pot() <= old(self).pot(),
    {
        if !self.at_start || self.buf.len() > 0 {
            return (false, Ghost(0));
        }
        if self.table.max > n {
            self.name_ref = 0;
            self.value_ref = 0;
            let g = self.table.resize(n);
            self.settings = n;
            self.pending = n;
            self.expect = true;
            (true, g)
        } else {
            self.settings = n;
            (true, Ghost(0))
        }
    }

    /// The header block ended (`nghttp2_hd_inflate_end_headers`).
    pub fn end_block(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).held_ok(),
            final(self).state() == end_block(old(self).state()),
            final(self).buf@.len() == 0,
            final(self).pot() <= old(self).pot() || !old(self).held_ok(),
    {
        self.at_start = true;
        self.expect = false;
        self.buf.clear();
        self.need = 0;
        self.name_end = 0;
    }
}

} // verus!
