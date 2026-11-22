//! The verified decoder: one field representation at a time (`rep`), and
//! the streaming wrapper that accepts input in arbitrary pieces (`feed`).
use crate::huffman;
use crate::integer::{self, IntE};
use crate::spec::*;
use crate::table::*;
use verilith_core::prims::extend;
use vstd::prelude::*;

verus! {

/// A decoder (one per HTTP/2 connection direction).
pub struct Decoder {
    pub table: Table,
    pub settings: u32,
    pub pending: u32,
    pub at_start: bool,
    pub expect: bool,
    /// The last field's name and value.
    pub name: Vec<u8>,
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
    /// are needed before it can be decoded.
    Short(usize),
    Bad,
    /// A field (in `name` and `value`), whether it is never-indexed, and
    /// the representation's length.
    Field(usize, bool),
    /// A dynamic table size update and its length.
    Update(usize),
}

pub enum StrE {
    Short(usize),
    Bad,
    Ok(usize),
}

/// Reads the string literal at `b[pos]` into `out`.
pub fn read_str(b: &[u8], pos: usize, out: &mut Vec<u8>, t: &[u32]) -> (r: StrE)
    requires
        huffman::layout_ok(),
        huffman::dtab_ok(t@),
        b@.len() + 0x2_0000 < usize::MAX,
    ensures
        match (r, str_dec(b@, pos as int)) {
            (StrE::Short(need), StrR::Short) => need > b@.len(),
            (StrE::Bad, StrR::Bad) => true,
            (StrE::Ok(e), StrR::Ok(s, se)) => e as int == se && final(out)@ == s && e <= b@.len(),
            _ => false,
        },
        final(out)@.len() <= 8 * MAX_STR,
{
    match integer::decode(b, pos, 7) {
        IntE::Short => {
            out.clear();
            StrE::Short(b.len() + 1)
        },
        IntE::Bad => {
            out.clear();
            StrE::Bad
        },
        IntE::Ok(n, e) => {
            if n > MAX_STR {
                out.clear();
                return StrE::Bad;
            }
            if n as usize > b.len() - e {
                out.clear();
                return StrE::Short(e + n as usize);
            }
            let raw = vstd::slice::slice_subrange(b, e, e + n as usize);
            proof {
                assert(raw@ == b@.subrange(e as int, e + n));
            }
            if b[pos] >= 128 {
                if huffman::decode(raw, out, t) {
                    StrE::Ok(e + n as usize)
                } else {
                    StrE::Bad
                }
            } else {
                out.clear();
                extend(out, raw);
                proof {
                    assert(out@ =~= raw@);
                }
                StrE::Ok(e + n as usize)
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
            r matches Some(d) ==> d.inv() && d.state() == initial() && d.buf@.len() == 0,
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
                (Step::Short(need), Rep::Short) => need > b@.len() && final(self).state() == old(self).state(),
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
        self.name_ref = 0;
        self.value_ref = 0;
        if b.len() == 0 {
            return Step::Short(1);
        }
        let c = b[0];
        if c & 0xE0 == 0x20 {
            if !self.at_start {
                return Step::Bad;
            }
            match integer::decode(b, 0, 5) {
                IntE::Short => Step::Short(b.len() + 1),
                IntE::Bad => Step::Bad,
                IntE::Ok(v, e) => {
                    let lim = if self.pending < self.settings { self.pending } else { self.settings };
                    if v > lim {
                        return Step::Bad;
                    }
                    self.table.resize(v);
                    self.pending = NO_LIMIT;
                    self.expect = false;
                    Step::Update(e)
                },
            }
        } else if self.expect {
            Step::Bad
        } else if c >= 0x80 {
            match integer::decode(b, 0, 7) {
                IntE::Short => Step::Short(b.len() + 1),
                IntE::Bad => Step::Bad,
                IntE::Ok(i, e) => {
                    if i == 0 || i as usize > self.table.len() + 61 {
                        return Step::Bad;
                    }
                    // The field is the entry: no copy.
                    self.name_ref = i as usize;
                    self.value_ref = i as usize;
                    self.at_start = false;
                    Step::Field(e, false)
                },
            }
        } else {
            let incr = c & 0x40 != 0;
            let never = c & 0xF0 == 0x10;
            let newname = c == 0x40 || c == 0x00 || c == 0x10;
            let e1 = if newname {
                match read_str(b, 1, &mut self.name, self.dt) {
                    StrE::Short(need) => return Step::Short(need),
                    StrE::Bad => return Step::Bad,
                    StrE::Ok(e) => e,
                }
            } else {
                match integer::decode(b, 0, if incr { 6 } else { 4 }) {
                    IntE::Short => return Step::Short(b.len() + 1),
                    IntE::Bad => return Step::Bad,
                    IntE::Ok(i, e) => {
                        if i == 0 || i as usize > self.table.len() + 61 {
                            return Step::Bad;
                        }
                        if incr {
                            let (n, _) = self.table.get(i as usize);
                            set(&mut self.name, n);
                        } else {
                            self.name_ref = i as usize;
                        }
                        e
                    },
                }
            };
            let e2 = match read_str(b, e1, &mut self.value, self.dt) {
                StrE::Short(need) => return Step::Short(need),
                StrE::Bad => return Step::Bad,
                StrE::Ok(e) => e,
            };
            if incr {
                // The buffers move into the table: the field is then its
                // newest entry.
                if self.table.insert_move(&mut self.name, &mut self.value) {
                    self.name_ref = 62;
                    self.value_ref = 62;
                }
            }
            self.at_start = false;
            Step::Field(e2, never)
        }
    }
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
    &&& 0 <= pos <= n
    &&& s.len() == ob + n
    &&& 0 <= k <= ob + pos
    &&& upd(st0, s, k) == Some(d.state())
    &&& d.buf@ == s.subrange(k, ob + pos)
    &&& d.buf@.len() <= MAX_BUF + n
    &&& n < 0x1000_0000
}

pub enum Next {
    Done(Feed),
    Go(usize),
}

impl Decoder {
    /// One round of `feed` with input buffered: completes the buffer from
    /// `input[pos..]` as far as worth it, then decodes it.
    #[verifier::rlimit(40)]
    fn feed_buffered(&mut self, input: &[u8], pos: usize, fin: bool, Ghost(st0): Ghost<DState>, Ghost(s): Ghost<Seq<u8>>, Ghost(ob): Ghost<int>, Ghost(k): Ghost<int>) -> (r: (Next, Ghost<int>))
        requires
            feed_inv(st0, s, ob, input@.len() as int, k, pos as int, *old(self)),
            s == s.subrange(0, ob) + input@,
            old(self).buf@.len() > 0,
            old(self).buf@.len() <= MAX_BUF,
        ensures
            match r.0 {
                Next::Done(f) => feed_ok(st0, s, ob, input@.len() as int, fin, f, *final(self)) && final(self).inv()
                    && final(self).buf@.len() <= MAX_BUF + input@.len(),
                Next::Go(p2) => {
                    &&& feed_inv(st0, s, ob, input@.len() as int, r.1@, p2 as int, *final(self))
                    &&& (s.len() - r.1@) + (input@.len() - p2) < (s.len() - k) + (input@.len() - pos)
                },
            },
    {
        let mut pos = pos;
        let avail = input.len() - pos;
        proof {
            assert(input@ =~= s.subrange(ob, s.len() as int));
        }
        if !fin && self.buf.len() + avail < self.need {
            extend(&mut self.buf, vstd::slice::slice_subrange(input, pos, input.len()));
            proof {
                assert(self.buf@ =~= s.subrange(k, s.len() as int));
            }
            return (Next::Done(Feed::More), Ghost(k));
        }
        let take = if fin || self.need <= self.buf.len() {
            avail
        } else if avail < self.need - self.buf.len() {
            avail
        } else {
            self.need - self.buf.len()
        };
        extend(&mut self.buf, vstd::slice::slice_subrange(input, pos, pos + take));
        pos = pos + take;
        proof {
            assert(self.buf@ =~= s.subrange(k, ob + pos));
        }
        let mut bb: Vec<u8> = Vec::new();
        core::mem::swap(&mut bb, &mut self.buf);
        let ghost s1 = self.state();
        let ghost rest = s.subrange(k, s.len() as int);
        let ghost more = s.subrange(ob + pos, s.len() as int);
        proof {
            assert(rest =~= bb@ + more);
        }
        match self.rep(bb.as_slice()) {
            Step::Short(need) => {
                self.need = need;
                self.buf = bb;
                if pos == input.len() {
                    proof {
                        assert(rest =~= bb@);
                    }
                    if fin {
                        self.buf.clear();
                        return (Next::Done(Feed::Bad), Ghost(k));
                    }
                    return (Next::Done(Feed::More), Ghost(k));
                }
                (Next::Go(pos), Ghost(k))
            },
            Step::Bad => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, bb@, more);
                }
                self.buf.clear();
                (Next::Done(Feed::Bad), Ghost(k))
            },
            Step::Update(e) => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, bb@, more);
                    crate::lemmas::lemma_upd_step(st0, s, k, s1, self.state(), e as int);
                }
                self.buf = tail(bb.as_slice(), e);
                self.need = 0;
                let ghost k2 = k + e;
                proof {
                    assert(self.buf@ =~= s.subrange(k2, ob + pos));
                }
                (Next::Go(pos), Ghost(k2))
            },
            Step::Field(e, never) => {
                proof {
                    crate::lemmas::lemma_rep_ext(s1, bb@, more);
                }
                self.buf = tail(bb.as_slice(), e);
                self.need = 0;
                proof {
                    assert(self.buf@ =~= s.subrange(k + e, ob + pos));
                    assert(upd(st0, s, k) == Some(s1));
                }
                (Next::Done(Feed::Field(pos, never)), Ghost(k))
            },
        }
    }

    /// One round of `feed` with nothing buffered: decodes `input[pos..]`.
    #[verifier::rlimit(40)]
    #[inline(always)]
    fn feed_direct(&mut self, input: &[u8], pos: usize, fin: bool, Ghost(st0): Ghost<DState>, Ghost(s): Ghost<Seq<u8>>, Ghost(ob): Ghost<int>, Ghost(k): Ghost<int>) -> (r: (Next, Ghost<int>))
        requires
            feed_inv(st0, s, ob, input@.len() as int, k, pos as int, *old(self)),
            s == s.subrange(0, ob) + input@,
            old(self).buf@.len() == 0,
        ensures
            match r.0 {
                Next::Done(f) => feed_ok(st0, s, ob, input@.len() as int, fin, f, *final(self)) && final(self).inv()
                    && final(self).buf@.len() <= MAX_BUF + input@.len(),
                Next::Go(p2) => {
                    &&& feed_inv(st0, s, ob, input@.len() as int, r.1@, p2 as int, *final(self))
                    &&& (s.len() - r.1@) + (input@.len() - p2) < (s.len() - k) + (input@.len() - pos)
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
                    return (Next::Done(Feed::Bad), Ghost(k));
                }
                return (Next::Done(Feed::Final), Ghost(k));
            }
            proof {
                assert(self.buf@ =~= s.subrange(k, s.len() as int));
            }
            return (Next::Done(Feed::More), Ghost(k));
        }
        let rest = vstd::slice::slice_subrange(input, pos, input.len());
        proof {
            assert(rest@ =~= s.subrange(k, s.len() as int));
        }
        let ghost s1 = self.state();
        match self.rep(rest) {
            Step::Short(need) => {
                if fin {
                    return (Next::Done(Feed::Bad), Ghost(k));
                }
                self.buf = tail(input, pos);
                self.need = need;
                (Next::Done(Feed::More), Ghost(k))
            },
            Step::Bad => (Next::Done(Feed::Bad), Ghost(k)),
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
                (Next::Go(p2), Ghost(k + e))
            },
            Step::Field(e, never) => {
                let p2 = pos + e;
                proof {
                    assert(self.buf@ =~= s.subrange(k + e, ob + p2));
                    assert(upd(st0, s, k) == Some(s1));
                }
                (Next::Done(Feed::Field(p2, never)), Ghost(k))
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
            input@.len() < 0x1000_0000,
            old(self).buf@.len() <= 0x2000_0000,
        ensures
            final(self).inv(),
            final(self).buf@.len() <= MAX_BUF + input@.len(),
            feed_ok(old(self).state(), old(self).buf@ + input@, old(self).buf@.len() as int, input@.len() as int, fin, r, *final(self)),
    {
        let ghost st0 = self.state();
        let ghost s = self.buf@ + input@;
        let ghost ob = self.buf@.len() as int;
        if self.buf.len() > MAX_BUF {
            self.buf.clear();
            proof {
                assert(upd(st0, s, 0) == Some(st0));
                assert(s.subrange(0, s.len() as int).len() > MAX_BUF);
            }
            return Feed::Bad;
        }
        let ghost mut k: int = 0;
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
            decreases (s.len() - k) + (input@.len() - pos),
        {
            let r = if self.buf.len() > 0 {
                if self.buf.len() > MAX_BUF {
                    self.buf.clear();
                    proof {
                        assert(s.subrange(k, s.len() as int).len() > MAX_BUF);
                    }
                    return Feed::Bad;
                }
                self.feed_buffered(input, pos, fin, Ghost(st0), Ghost(s), Ghost(ob), Ghost(k))
            } else {
                self.feed_direct(input, pos, fin, Ghost(st0), Ghost(s), Ghost(ob), Ghost(k))
            };
            match r.0 {
                Next::Done(f) => return f,
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
        ensures
            final(self).inv(),
            final(self).buf == old(self).buf,
            ok == (old(self).at_start && old(self).buf@.len() == 0),
            ok ==> final(self).state() == change_settings(old(self).state(), n as nat),
            !ok ==> final(self).state() == old(self).state(),
    {
        if !self.at_start || self.buf.len() > 0 {
            return false;
        }
        if self.table.max > n {
            self.name_ref = 0;
            self.value_ref = 0;
            self.table.resize(n);
            self.settings = n;
            self.pending = n;
            self.expect = true;
        } else {
            self.settings = n;
        }
        true
    }

    /// The header block ended (`nghttp2_hd_inflate_end_headers`).
    pub fn end_block(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).state() == end_block(old(self).state()),
            final(self).buf@.len() == 0,
    {
        self.at_start = true;
        self.expect = false;
        self.buf.clear();
        self.need = 0;
    }
}

} // verus!
