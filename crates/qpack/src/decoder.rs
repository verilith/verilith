//! The verified decoder: the encoder stream (`feed_encoder`), field
//! sections (`decode`), stream cancellation (`cancel`) and the decoder
//! stream it writes (`take_output`).
use crate::integer::{self, IntE};
use crate::lemmas::*;
use crate::spec::*;
use crate::strings::{self, EndE, StrE};
use crate::table::*;
use std::rc::Rc;
use verilith_core::prims::extend;
use verilith_hpack::huffman;
use vstd::prelude::*;

verus! {

/// The blocked streams, as the spec sees them.
pub open spec fn bview(v: Seq<(u64, u64)>) -> Seq<(nat, nat)> {
    Seq::new(v.len(), |i: int| (v[i].0 as nat, v[i].1 as nat))
}

/// The stream ids of `bl`.
pub open spec fn sids(bl: Seq<(nat, nat)>) -> Seq<nat> {
    Seq::new(bl.len(), |i: int| bl[i].0)
}

pub open spec fn nats(v: Seq<u64>) -> Seq<nat> {
    Seq::new(v.len(), |i: int| v[i] as nat)
}

/// A copy of `s`.
pub fn to_vec(s: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == s@,
{
    let mut r = Vec::with_capacity(s.len());
    extend(&mut r, s);
    proof {
        assert(r@ =~= s@);
    }
    r
}

/// Frames the encoder instruction at the start of `b` (`spec::eframe`).
pub fn eframe_x(b: &[u8], mc: u64) -> (r: EndE)
    requires
        mc <= CAP_LIMIT,
    ensures
        strings::end_matches(r, eframe(b@, mc as nat)),
        r matches EndE::Ok(e) ==> 0 < e <= b@.len() && e <= 2 * str_limit(mc as nat) + 20,
{
    proof {
        reveal(eframe);
    }
    let lim = 4 * mc + 8;
    if b.len() == 0 {
        return EndE::Short;
    }
    if b[0] >= 0x80 {
        match integer::decode(b, 0, 6) {
            IntE::Short => EndE::Short,
            IntE::Bad => EndE::Bad,
            IntE::Ok(_, e) => strings::end(b, e, 8, lim),
        }
    } else if b[0] >= 0x40 {
        match strings::end(b, 0, 6, lim) {
            EndE::Ok(e) => strings::end(b, e, 8, lim),
            EndE::Short => EndE::Short,
            EndE::Bad => EndE::Bad,
        }
    } else {
        match integer::decode(b, 0, 5) {
            IntE::Short => EndE::Short,
            IntE::Bad => EndE::Bad,
            IntE::Ok(_, e) => EndE::Ok(e),
        }
    }
}

/// Applies the encoder instruction `b` (exactly one, as framed) to the
/// table (`spec::einst`). The second result is the work: strings decoded
/// or copied, and entries evicted.
pub fn apply(t: &mut DynTable, b: &[u8], mc: u64, dt: &[u32]) -> (r: (bool, Ghost<nat>))
    requires
        old(t).inv(),
        old(t).cap <= mc,
        mc <= CAP_LIMIT,
        huffman::layout_ok(),
        huffman::dtab_ok(dt@),
        1 <= b@.len() <= 0x1000_0000,
    ensures
        final(t).inv(),
        final(t).cap <= mc,
        match einst(old(t).view(), mc as nat, b@) {
            Some(t2) => r.0 && final(t).view() == t2,
            None => !r.0,
        },
        r.0 ==> r.1@ + final(t).view().ents.len() <= old(t).view().ents.len() + 13 * b@.len(),
{
    proof {
        reveal(einst);
        integer::lemma_pows();
    }
    let lim = 4 * mc + 8;
    if b[0] >= 0x80 {
        match integer::decode(b, 0, 6) {
            IntE::Ok(i, e) => {
                let mut v: Vec<u8> = Vec::new();
                let (sr, g) = strings::read(b, e, 8, lim, &mut v, dt);
                match sr {
                    StrE::Ok(_) => {},
                    _ => {
                        return (false, g);
                    },
                }
                let name: Rc<Vec<u8>> = if b[0] >= 0xC0 {
                    if i >= STATIC_LEN {
                        return (false, g);
                    }
                    Rc::new(to_vec(static_entry(i as usize).0))
                } else {
                    if i >= t.len() {
                        return (false, g);
                    }
                    Rc::clone(&t.rel(i).name)
                };
                let (ok, g2) = t.insert(Ent { name, value: Rc::new(v) });
                (ok, Ghost(g@ + g2@))
            },
            _ => (false, Ghost(0)),
        }
    } else if b[0] >= 0x40 {
        let mut n: Vec<u8> = Vec::new();
        let (sr, g) = strings::read(b, 0, 6, lim, &mut n, dt);
        let e = match sr {
            StrE::Ok(e) => e,
            _ => {
                return (false, g);
            },
        };
        let mut v: Vec<u8> = Vec::new();
        let (sr2, g2) = strings::read(b, e, 8, lim, &mut v, dt);
        match sr2 {
            StrE::Ok(_) => {},
            _ => {
                return (false, Ghost(g@ + g2@));
            },
        }
        let (ok, g3) = t.insert(Ent { name: Rc::new(n), value: Rc::new(v) });
        (ok, Ghost(g@ + g2@ + g3@))
    } else if b[0] >= 0x20 {
        match integer::decode(b, 0, 5) {
            IntE::Ok(c, _) => {
                if c > mc {
                    return (false, Ghost(0));
                }
                let g = t.set_cap(c);
                (true, g)
            },
            _ => (false, Ghost(0)),
        }
    } else {
        match integer::decode(b, 0, 5) {
            IntE::Ok(i, _) => {
                if i >= t.len() {
                    return (false, Ghost(0));
                }
                let en = t.rel(i);
                let e2 = Ent { name: Rc::clone(&en.name), value: Rc::clone(&en.value) };
                let (ok, g) = t.insert(e2);
                (ok, g)
            },
            _ => (false, Ghost(0)),
        }
    }
}

/// Applies the whole instructions at the start of `b` (`spec::erun`): how
/// many bytes they take, or `None` on an error. The second result is the
/// work: each instruction's (`apply`) and one step per turn of the loop.
pub fn run(t: &mut DynTable, b: &[u8], mc: u64, dt: &[u32]) -> (r: (Option<usize>, Ghost<nat>))
    requires
        old(t).inv(),
        old(t).cap <= mc,
        mc <= CAP_LIMIT,
        huffman::layout_ok(),
        huffman::dtab_ok(dt@),
    ensures
        final(t).inv(),
        final(t).cap <= mc,
        match erun(old(t).view(), mc as nat, b@) {
            Run::Bad => r.0 is None,
            Run::Ok(t2, k) => r.0 == Some(k as usize) && final(t).view() == t2,
        },
        r.0 matches Some(k) ==> r.1@ + final(t).view().ents.len() <= old(t).view().ents.len() + 14 * k + 1,
{
    let ghost t0 = t.view();
    let ghost mut steps: nat = 0;
    let mut pos: usize = 0;
    proof {
        assert(b@.subrange(0, b@.len() as int) =~= b@);
    }
    loop
        invariant
            pos <= b@.len(),
            t.inv(),
            t.cap <= mc,
            mc <= CAP_LIMIT,
            huffman::layout_ok(),
            huffman::dtab_ok(dt@),
            t0 == old(t).view(),
            erun(t0, mc as nat, b@) == shift(erun(t.view(), mc as nat, b@.subrange(pos as int, b@.len() as int)), pos as int),
            steps + t.view().ents.len() <= t0.ents.len() + 14 * pos,
        decreases b@.len() - pos,
    {
        let rest = vstd::slice::slice_subrange(b, pos, b.len());
        proof {
            assert(rest@ == b@.subrange(pos as int, b@.len() as int));
        }
        match eframe_x(rest, mc) {
            EndE::Short => {
                proof {
                    assert(erun(t.view(), mc as nat, rest@) == Run::Ok(t.view(), 0));
                    assert(shift(erun(t.view(), mc as nat, rest@), pos as int) == Run::Ok(t.view(), pos as int));
                    assert(erun(t0, mc as nat, b@) == Run::Ok(t.view(), pos as int));
                }
                return (Some(pos), Ghost(steps + 1));
            },
            EndE::Bad => {
                return (None, Ghost(steps + 1));
            },
            EndE::Ok(e) => {
                let ins = vstd::slice::slice_subrange(rest, 0, e);
                proof {
                    assert(ins@ == rest@.subrange(0, e as int));
                    assert(str_limit(mc as nat) <= 4 * CAP_LIMIT + 8);
                }
                let ghost tv = t.view();
                let ghost n0 = t.view().ents.len();
                let (ok, g) = apply(t, ins, mc, dt);
                if !ok {
                    return (None, Ghost(steps + g@ + 1));
                }
                proof {
                    let r2 = rest@.subrange(e as int, rest@.len() as int);
                    assert(r2 =~= b@.subrange(pos + e, b@.len() as int));
                    match erun(t.view(), mc as nat, r2) {
                        Run::Bad => {},
                        Run::Ok(_, _) => {},
                    }
                    steps = steps + g@ + 1;
                }
                pos = pos + e;
            },
        }
    }
}

/// A QPACK decoder (one per HTTP/3 connection): it reads the peer's encoder
/// stream and field sections, and writes the decoder stream.
pub struct Decoder {
    pub table: DynTable,
    /// SETTINGS_QPACK_MAX_TABLE_CAPACITY, as sent.
    pub max_cap: u64,
    /// SETTINGS_QPACK_BLOCKED_STREAMS, as sent.
    pub max_blocked: u64,
    /// SETTINGS_MAX_FIELD_SECTION_SIZE, as sent.
    pub max_size: u64,
    /// The blocked streams and the Required Insert Count each waits for.
    pub blocked: Vec<(u64, u64)>,
    /// The Known Received Count the encoder can work out.
    pub acked: u64,
    /// Decoder stream bytes not yet taken.
    pub out: Vec<u8>,
    /// The start of an encoder instruction that has not fully arrived.
    pub held: Vec<u8>,
    /// The Huffman decoding table.
    pub dt: &'static [u32],
}

impl Decoder {
    pub open spec fn state(&self) -> DecState {
        DecState {
            table: self.table.view(),
            max_cap: self.max_cap as nat,
            max_blocked: self.max_blocked as nat,
            max_size: self.max_size as nat,
            blocked: bview(self.blocked@),
            acked: self.acked as nat,
            out: self.out@,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.table.inv()
        &&& self.table.cap <= self.max_cap
        &&& self.max_cap <= CAP_LIMIT
        &&& huffman::layout_ok()
        &&& huffman::dtab_ok(self.dt@)
        &&& eframe(self.held@, self.max_cap as nat) is Short
    }

    /// The potential of the work bound: 16 per held byte (which pays for
    /// decoding it once its instruction is whole) and 1 per table entry
    /// (which pays for evicting it).
    pub open spec fn pot(&self) -> nat {
        16 * self.held@.len() + self.table.view().ents.len()
    }

    /// A decoder that announced these settings. `None` if `max_cap` is over
    /// `CAP_LIMIT` (or the Huffman table check fails, which it does not).
    pub fn new(max_cap: u64, max_blocked: u64, max_size: u64) -> (r: Option<Decoder>)
        ensures
            r matches Some(d) ==> d.inv() && d.held@.len() == 0 && d.state() == (DecState {
                table: empty_table(),
                max_cap: max_cap as nat,
                max_blocked: max_blocked as nat,
                max_size: max_size as nat,
                blocked: Seq::empty(),
                acked: 0,
                out: Seq::empty(),
            }),
    {
        if max_cap > CAP_LIMIT {
            return None;
        }
        let dt = match huffman::dtab() {
            Some(t) => t,
            None => {
                return None;
            },
        };
        let d = Decoder {
            table: DynTable::new(),
            max_cap,
            max_blocked,
            max_size,
            blocked: Vec::new(),
            acked: 0,
            out: Vec::new(),
            held: Vec::new(),
            dt,
        };
        proof {
            reveal(eframe);
            assert(d.state().blocked =~= Seq::<(nat, nat)>::empty());
        }
        Some(d)
    }

    /// Releases the blocked streams whose Required Insert Count is reached,
    /// appending their ids to `unblocked`, and tells the encoder of new
    /// entries (Insert Count Increment).
    fn after_inserts(&mut self, ready: &mut Vec<u64>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).held@ == old(self).held@,
            final(self).state() == ({
                let st = old(self).state();
                let n = icount(st.table);
                let st2 = DecState { blocked: still_blocked(st.blocked, n), ..st };
                if n > st.acked {
                    DecState { out: st2.out + insert_count_inc((n - st.acked) as nat), acked: n, ..st2 }
                } else {
                    st2
                }
            }),
            nats(final(ready)@) == nats(old(ready)@) + sids(unblocked(old(self).state().blocked, icount(old(self).table.view()))),
    {
        let n = self.table.icount();
        let ghost bl = bview(self.blocked@);
        let mut kept: Vec<(u64, u64)> = Vec::new();
        let mut i: usize = 0;
        proof {
            assert(bl.subrange(0, 0) =~= Seq::<(nat, nat)>::empty());
            assert(bview(kept@) =~= Seq::<(nat, nat)>::empty());
            assert(sids(Seq::<(nat, nat)>::empty()) =~= Seq::<nat>::empty());
            assert(nats(ready@) =~= nats(old(ready)@) + Seq::<nat>::empty());
        }
        while i < self.blocked.len()
            invariant
                i <= self.blocked@.len(),
                bl == bview(self.blocked@),
                n == icount(self.table.view()),
                bview(kept@) == still_blocked(bl.subrange(0, i as int), n as nat),
                nats(ready@) == nats(old(ready)@) + sids(unblocked(bl.subrange(0, i as int), n as nat)),
            decreases self.blocked@.len() - i,
        {
            let (s, ric) = self.blocked[i];
            let ghost pre = bl.subrange(0, i as int);
            let ghost pre2 = bl.subrange(0, i + 1);
            proof {
                assert(pre2.drop_last() =~= pre);
                assert(pre2.last() == (s as nat, ric as nat));
            }
            if ric <= n {
                let ghost u0 = ready@;
                ready.push(s);
                proof {
                    assert(nats(ready@) =~= nats(u0).push(s as nat));
                    assert(sids(unblocked(pre2, n as nat)) =~= sids(unblocked(pre, n as nat)).push(s as nat));
                    assert(nats(old(ready)@) + sids(unblocked(pre2, n as nat)) =~= (nats(old(ready)@) + sids(unblocked(pre, n as nat))).push(s as nat));
                }
            } else {
                let ghost k0 = kept@;
                kept.push((s, ric));
                proof {
                    assert(bview(kept@) =~= bview(k0).push((s as nat, ric as nat)));
                }
            }
            i = i + 1;
        }
        proof {
            assert(bl.subrange(0, bl.len() as int) =~= bl);
        }
        self.blocked = kept;
        if n > self.acked {
            proof {
                integer::lemma_pows();
                assert(integer::P2@[6] as nat == p2(6));
            }
            integer::encode(&mut self.out, 0, 6, n - self.acked);
            self.acked = n;
        }
    }

    /// Reads encoder stream bytes, in pieces of any size
    /// (`spec::dec_feed`); false on QPACK_ENCODER_STREAM_ERROR. Streams this
    /// unblocks are appended to `unblocked`: decode their sections again.
    pub fn feed_encoder(&mut self, input: &[u8], ready: &mut Vec<u64>) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            match dec_feed(old(self).state(), old(self).held@, input@) {
                None => !ok,
                Some((st, rest)) => ok && final(self).inv() && final(self).state() == st && final(self).held@ == rest
                    && nats(final(ready)@) == nats(old(ready)@) + sids(unblocked(old(self).state().blocked, icount(st.table))),
            },
    {
        self.feed_encoder_metered(input, ready).0
    }

    /// `feed_encoder`, and its work. Over any sequence of calls the work
    /// is at most 18 steps per input byte, plus 1 and the number of
    /// blocked streams per call: `pot` is 0 for a new decoder and never
    /// negative.
    pub fn feed_encoder_metered(&mut self, input: &[u8], ready: &mut Vec<u64>) -> (r: (bool, Ghost<nat>))
        requires
            old(self).inv(),
        ensures
            match dec_feed(old(self).state(), old(self).held@, input@) {
                None => !r.0,
                Some((st, rest)) => r.0 && final(self).inv() && final(self).state() == st && final(self).held@ == rest
                    && nats(final(ready)@) == nats(old(ready)@) + sids(unblocked(old(self).state().blocked, icount(st.table))),
            },
            r.0 ==> r.1@ + final(self).pot() <= old(self).pot() + 18 * input@.len() + 1 + old(self).blocked@.len(),
    {
        let ghost st0 = self.state();
        let ghost h0 = self.held@;
        let ghost all = h0 + input@;
        let mc = self.max_cap;
        let ghost steps: nat;
        if self.held.len() == 0 {
            proof {
                assert(all =~= input@);
            }
            let (k, g) = run(&mut self.table, input, mc, self.dt);
            let k = match k {
                Some(k) => k,
                None => {
                    return (false, Ghost(0));
                },
            };
            proof {
                lemma_erun_rest(st0.table, mc as nat, input@);
            }
            let rest = vstd::slice::slice_subrange(input, k, input.len());
            extend(&mut self.held, rest);
            proof {
                assert(self.held@ =~= all.subrange(k as int, all.len() as int));
                steps = g@ + rest@.len();
            }
        } else {
            let ghost hl = h0.len();
            extend(&mut self.held, input);
            proof {
                assert(self.held@ =~= all);
            }
            let (k, g) = run(&mut self.table, self.held.as_slice(), mc, self.dt);
            let k = match k {
                Some(k) => k,
                None => {
                    return (false, Ghost(0));
                },
            };
            proof {
                lemma_erun_rest(st0.table, mc as nat, all);
                lemma_erun_first(st0.table, mc as nat, all);
                assert(all.subrange(0, hl as int) =~= h0);
                lemma_eframe_short_prefix(all, hl as int, mc as nat);
            }
            if k > 0 {
                let rest = to_vec(vstd::slice::slice_subrange(self.held.as_slice(), k, self.held.len()));
                proof {
                    assert(k > hl);
                    steps = input@.len() + g@ + rest@.len();
                }
                self.held = rest;
            } else {
                proof {
                    assert(self.held@ =~= all.subrange(0, all.len() as int));
                    steps = input@.len() + g@;
                }
            }
        }
        let ghost before = self.state();
        self.after_inserts(ready);
        (true, Ghost(steps + st0.blocked.len()))
    }

    /// Hands over the decoder stream bytes written so far.
    pub fn take_output(&mut self, dst: &mut Vec<u8>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(dst)@ == old(dst)@ + old(self).out@,
            final(self).state() == (DecState { out: Seq::empty(), ..old(self).state() }),
            final(self).held@ == old(self).held@,
    {
        extend(dst, self.out.as_slice());
        self.out.clear();
    }

    /// Stream `stream` was reset or abandoned (`spec::dec_cancel`).
    pub fn cancel(&mut self, stream: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).state() == dec_cancel(old(self).state(), stream as nat),
            final(self).held@ == old(self).held@,
    {
        self.unblock(stream);
        if self.max_cap > 0 {
            proof {
                integer::lemma_pows();
                assert(integer::P2@[6] as nat == p2(6));
            }
            integer::encode(&mut self.out, 0x40, 6, stream);
        }
    }

    /// Removes `stream` from the blocked streams.
    fn unblock(&mut self, stream: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).state() == (DecState { blocked: without(old(self).state().blocked, stream as nat), ..old(self).state() }),
            final(self).held@ == old(self).held@,
    {
        let ghost bl = bview(self.blocked@);
        let mut kept: Vec<(u64, u64)> = Vec::new();
        let mut i: usize = 0;
        proof {
            assert(bl.subrange(0, 0) =~= Seq::<(nat, nat)>::empty());
            assert(bview(kept@) =~= Seq::<(nat, nat)>::empty());
        }
        while i < self.blocked.len()
            invariant
                i <= self.blocked@.len(),
                bl == bview(self.blocked@),
                bview(kept@) == without(bl.subrange(0, i as int), stream as nat),
            decreases self.blocked@.len() - i,
        {
            let (s, ric) = self.blocked[i];
            let ghost pre = bl.subrange(0, i as int);
            let ghost pre2 = bl.subrange(0, i + 1);
            proof {
                assert(pre2.drop_last() =~= pre);
                assert(pre2.last() == (s as nat, ric as nat));
            }
            if s != stream {
                let ghost k0 = kept@;
                kept.push((s, ric));
                proof {
                    assert(bview(kept@) =~= bview(k0).push((s as nat, ric as nat)));
                }
            }
            i = i + 1;
        }
        proof {
            assert(bl.subrange(0, bl.len() as int) =~= bl);
        }
        self.blocked = kept;
    }
}

} // verus!
