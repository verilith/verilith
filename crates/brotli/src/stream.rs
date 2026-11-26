//! Streaming decompression, the way `BrotliDecoderDecompressStream` works:
//! input and output in pieces of any size.
//!
//! The theorem is stated, as in vzlib, for a ghost `full` stream fixed when
//! the `Stream` is made: as long as each call's input is the next piece of
//! `full`, every byte delivered is the spec's, `Success` means the spec
//! decodes `full` to exactly the output delivered, and `Error` means the
//! spec rejects `full` (or its output would pass `decoder::MAX_OUT`).
//! Since `full` is arbitrary, this holds for whatever the stream turns out
//! to be.
//!
//! The decoder reads at absolute bit positions of the whole stream. Most of
//! the time it reads straight from the caller's input. When the input ends
//! inside an item, the bytes from the item's start are kept in `tail`; the
//! next call appends a little of its input to `tail` and decodes from there
//! until the decoder is past the bytes kept, then goes back to reading the
//! caller's input directly, handing back what it appended past that point.
use crate::decoder::*;
use crate::work::*;
#[cfg(verus_only)]
use crate::bitread::*;
#[cfg(verus_only)]
use crate::spec;
#[cfg(verus_only)]
use crate::rank::*;
use vstd::prelude::*;

verus! {

/// What one call did.
#[derive(Clone, Copy, PartialEq, Eq, Structural)]
pub enum Result {
    /// The stream is malformed (or its output too large).
    Error,
    /// The stream ended and all its output was handed out.
    Success,
    /// All input was used; more is needed.
    NeedsMoreInput,
    /// The output buffer is full; more output is waiting.
    NeedsMoreOutput,
}

/// How many input bytes to add to `tail` at a time.
pub const TAIL_STEP: usize = 64;

/// How many steps `Decoder::run` takes before it returns to check output.
pub const BUDGET: u64 = 0x10_0000;

pub struct Stream {
    pub dec: Decoder,
    /// Input bytes kept from earlier calls: `full[tail_base..used]`.
    pub tail: Vec<u8>,
    pub tail_base: u64,
    pub bad: bool,
    pub done: bool,
    /// The whole stream, for the proofs.
    pub full: Ghost<Seq<u8>>,
    /// Bytes of `full` used so far (handed in and not handed back).
    pub used: Ghost<nat>,
    /// Bytes handed out so far.
    pub dlv: Ghost<Seq<u8>>,
    /// `bad` because the output would pass `MAX_OUT`.
    pub limit: Ghost<bool>,
    /// The decoder's steps so far.
    pub steps: Ghost<nat>,
}

/// What a round of decoding did, from `o` to `n`, returning `r`.
pub open spec fn round_ok(o: Stream, n: Stream, r: (Status, usize), len: nat, u0: nat) -> bool {
    &&& n.inv()
    &&& n.full == o.full
    &&& n.dlv == o.dlv
    &&& n.done == o.done
    &&& r.1 <= len
    &&& n.used@ == u0 + r.1
    &&& ((r.0 == Status::Bad || r.0 == Status::Limit) <==> n.bad)
    &&& (!n.bad ==> n.dec.flushed == o.dec.flushed && (r.0 == Status::Done ==> n.dec.ph == Ph::Done))
    // Progress: the decoder stepped, or stopped for input or output.
    &&& r.1 >= o.used@ - u0
    &&& (!n.bad ==> n.dec == o.dec || rank_lt(n.full@, n.dec.view(), o.dec.view()))
    &&& (!n.bad && r.0 == Status::Yield ==> rank_lt(n.full@, n.dec.view(), o.dec.view()))
    &&& (!n.bad && r.0 == Status::Full ==> n.dec.total > n.dec.flushed)
    // Stopping for input with all of it in: the spec stops too.
    &&& (!n.bad && r.0 == Status::Short && n.used@ == n.full@.len() ==> spec::step(n.full@, n.dec.view()) is Short)
}

/// The work of a round from `o` to `n` that took `r.0`, with `input`
/// and `ip` as it was given: what its bits pay for, and two steps for a
/// round that stopped for a reason other than its step budget. A round
/// that finds the stream malformed may have read all of `input` and pays
/// the most such a step does.
pub open spec fn round_work(o: Stream, n: Stream, r: (Status, usize), ilen: nat, ip: nat) -> bool {
    if n.bad {
        n.work() <= o.work() + 8 * kbit() * (ilen - ip) + xc() + 1
    } else {
        n.work() + 2 * o.tl() <= o.work() + 8 * kbit() * (n.used@ - o.used@) + (if r.0 == Status::Yield { 0int } else { 2int })
            + 2 * n.tl()
    }
}

/// The stream decodes, with output small enough, and the call gets the
/// rest of the input and room for the rest of the output.
pub open spec fn complete(s: Stream, ilen: nat, olen: nat) -> bool {
    &&& s.used@ + ilen == s.full@.len()
    &&& exists|o: Seq<u8>, u: int| #[trigger] spec::decodes(s.full@, o, u) && s.dlv@.len() + olen >= o.len()
        && o.len() + 0x1_0000_0000 <= MAX_OUT
}

impl Stream {
    pub open spec fn inv(&self) -> bool {
        let b = self.full@;
        &&& b.len() <= MAX_INPUT
        &&& self.used@ <= b.len()
        &&& (!self.bad ==> {
            &&& self.dec.wf()
            &&& self.dec.reached(b)
            &&& self.dlv@ == self.dec.out@.subrange(0, self.dec.flushed as int)
            &&& (self.done ==> self.dec.ph == Ph::Done)
            &&& if self.tail@.len() == 0 {
                8 * self.used@ <= self.dec.pos < 8 * self.used@ + 8
            } else {
                &&& self.tail_base + self.tail@.len() == self.used@
                &&& self.tail@ == b.subrange(self.tail_base as int, self.used@ as int)
                &&& 8 * self.tail_base <= self.dec.pos <= 8 * self.used@
            }
        })
        &&& (!self.bad ==> self.dec.pos <= 8 * b.len())
        &&& (self.bad && !self.limit@ ==> spec::rejects(b))
        &&& (self.bad && self.limit@ ==> exists|t: spec::St| #[trigger] spec::reaches(b, t) && t.out.len()
            + 0x1_0000_0000 > MAX_OUT)
    }

    /// Whether bytes are kept in `tail`.
    pub open spec fn tl(&self) -> int {
        if self.tail@.len() > 0 {
            1
        } else {
            0
        }
    }

    /// The steps paid for in advance: the decoder's credit, the bits of
    /// the input taken but not read yet, the output not handed out yet,
    /// and a round for the bytes kept.
    pub open spec fn credit(&self) -> int {
        if self.bad {
            0
        } else {
            pot(self.dec) + 3 + kbit() * (8 * self.used@ + 8 - self.dec.pos) + lbyte() * (rmax() - (self.dec.total
                - self.dec.flushed)) + 2 * self.tl()
        }
    }

    /// The steps so far plus the credit: what the work bound is about.
    pub open spec fn work(&self) -> int {
        self.steps@ + self.credit()
    }

    /// The steps so far are at most `work()`.
    pub proof fn lemma_steps(&self)
        requires
            self.inv(),
        ensures
            self.steps@ <= self.work(),
    {
        if !self.bad {
            lemma_pot_lb(self.dec);
            lemma_ring_basic(self.dec);
        }
    }

    #[verifier::spinoff_prover]
    pub fn new(Ghost(full): Ghost<Seq<u8>>) -> (r: Stream)
        requires
            full.len() <= MAX_INPUT,
        ensures
            r.inv(),
            r.full@ == full,
            r.used@ == 0,
            r.dlv@ == Seq::<u8>::empty(),
            r.steps@ == 0,
            r.work() == 12 * rmax() + 8 * kbit() + 3,
    {
        let dec = Decoder::new();
        let r = Stream {
            dec,
            tail: Vec::new(),
            tail_base: 0,
            bad: false,
            done: false,
            full: Ghost(full),
            used: Ghost(0),
            dlv: Ghost(Seq::empty()),
            limit: Ghost(false),
            steps: Ghost(0),
        };
        proof {
            assert(r.dec.out@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        r
    }

    /// `new` for callers with no ghost `full` to give. The ghost stream is
    /// empty, so the proofs about `full` say nothing past the first byte.
    pub fn open() -> (r: Stream)
        ensures
            r.inv(),
    {
        Stream::new(Ghost(Seq::empty()))
    }

    /// Output decoded but not handed out yet.
    pub fn has_more_output(&self) -> bool
        requires
            self.inv(),
    {
        !self.bad && self.dec.pending() > 0
    }

    /// The stream ended and all of its output was handed out.
    pub fn is_finished(&self) -> bool
        requires
            self.inv(),
    {
        !self.bad && self.done && self.dec.pending() == 0
    }

    /// Decodes from `input` into `output`. Returns what happened, how much
    /// input was used and how much output was written.
    ///
    /// Every call returns (the loop's measure is the decoder's rank, then
    /// output handed out, input taken, and bytes kept). And a stream that
    /// decodes, given all of its remaining input and room for all of its
    /// remaining output, finishes in this call with `Success`.
    #[verifier::spinoff_prover]
    #[verifier::loop_isolation(false)]
    #[verifier::rlimit(40)]
    pub fn decompress(&mut self, input: &[u8], output: &mut [u8]) -> (r: (Result, usize, usize))
        requires
            old(self).inv(),
            old(self).used@ + input@.len() <= old(self).full@.len(),
            input@ == old(self).full@.subrange(old(self).used@ as int, (old(self).used@ + input@.len()) as int),
        ensures
            final(self).inv(),
            final(self).full == old(self).full,
            final(output)@.len() == old(output)@.len(),
            r.1 <= input@.len(),
            r.2 <= old(output)@.len(),
            final(self).used@ == old(self).used@ + r.1,
            final(self).dlv@ == old(self).dlv@ + final(output)@.subrange(0, r.2 as int),
            // Everything handed out is output the spec reaches.
            !final(self).bad ==> spec::reaches(final(self).full@, final(self).dec.view())
                && final(self).dlv@.is_prefix_of(final(self).dec.view().out),
            r.0 == Result::Success ==> final(self).dec.pos / 8 <= final(self).used@ && spec::decodes(
                final(self).full@,
                final(self).dlv@,
                (final(self).dec.pos / 8) as int,
            ),
            r.0 == Result::Error <==> final(self).bad,
            // Completeness.
            complete(*old(self), input@.len(), old(output)@.len()) ==> r.0 == Result::Success,
            // Linear work.
            final(self).work() <= old(self).work() + (8 * kbit() + 2) * r.1 + 10 * r.2 + xc() + 16 + (if r.0
                == Result::Error { 8 * kbit() * input@.len() } else { 0 }),
    {
        hide(Stream::work);
        let ghost b = self.full@;
        let ghost u0 = self.used@;
        let ghost d0 = self.dlv@;
        let ghost out0 = output@;
        let ghost cpl = complete(*self, input@.len(), output@.len());
        let ghost w0 = self.work();
        let ghost fo: Seq<u8> = Seq::empty();
        let ghost fu: int = 0;
        let ghost fst: spec::St = spec::init();
        let ghost fnn: nat = 0;
        proof {
            if cpl {
                let (o, u) = choose|o: Seq<u8>, u: int| #[trigger] spec::decodes(b, o, u)
                    && d0.len() + out0.len() >= o.len() && o.len() + 0x1_0000_0000 <= MAX_OUT;
                fo = o;
                fu = u;
                fst = choose|f: spec::St| #[trigger] spec::reaches(b, f) && f.phase is Done && f.out == o
                    && 8 * u == f.pos;
                fnn = choose|nn: nat| spec::run(b, spec::init(), nn) == spec::Step::Next(fst);
                lemma_decodes_not_rejects(b, fo, fu);
                if self.bad && self.limit@ {
                    let t = choose|t: spec::St| #[trigger] spec::reaches(b, t) && t.out.len() + 0x1_0000_0000
                        > MAX_OUT;
                    let k = choose|k: nat| spec::run(b, spec::init(), k) == spec::Step::Next(t);
                    lemma_on_way(b, k, t, fnn, fst);
                }
            }
        }
        if self.bad {
            return (Result::Error, 0, 0);
        }
        proof {
            assert(output@.subrange(0, 0) =~= Seq::<u8>::empty());
            assert(d0 =~= d0 + output@.subrange(0, 0));
        }
        let mut ip: usize = 0;
        let mut op: usize = 0;
        proof {
            lemma_ring_basic(self.dec);
        }
        loop
            invariant
                self.inv(),
                !self.bad,
                self.full@ == b,
                ip <= input@.len(),
                op <= output@.len(),
                output@.len() == out0.len(),
                self.used@ == u0 + ip,
                self.dlv@ == d0 + output@.subrange(0, op as int),
                self.dec.flushed <= MAX_OUT,
                self.work() <= w0 + 8_000_002 * ip + 10 * op + (if self.done { 2int } else { 0int }),
                cpl ==> {
                    &&& spec::run(b, spec::init(), fnn) == spec::Step::Next(fst)
                    &&& fst.phase is Done
                    &&& fst.out == fo
                    &&& d0.len() + out0.len() >= fo.len()
                    &&& fo.len() + 0x1_0000_0000 <= MAX_OUT
                    &&& u0 + input@.len() == b.len()
                    &&& !spec::rejects(b)
                },
            decreases
                (if self.done { 0int } else { 1int }),
                rk(b, self.dec.view()).0,
                rk(b, self.dec.view()).1,
                rk(b, self.dec.view()).2,
                rk(b, self.dec.view()).3,
                rk(b, self.dec.view()).4,
                MAX_OUT - self.dec.flushed,
                input@.len() - ip,
                (if self.tail@.len() > 0 { 1int } else { 0int }),
        {
            let ghost dec0 = self.dec;
            let ghost ip0 = ip;
            proof {
                lemma_kb(input@.len() as int, ip as int);
            }
            let ghost tl0 = self.tail@.len();
            op = self.flush_to(output, op, Ghost(d0));
            let ghost dec1 = self.dec;
            let ghost wk1 = self.work();
            let ghost s1 = *self;
            assert(wk1 <= w0 + 8_000_002 * ip + 10 * op + (if self.done { 2int } else { 0int }));
            proof {
                lemma_ring_basic(self.dec);
                if cpl {
                    lemma_reaches(self.dec, b);
                    lemma_on_way(b, self.dec.steps@, self.dec.view(), fnn, fst);
                    // What is handed out fits in the output the stream has.
                    assert(self.dlv@.len() == d0.len() + op);
                    assert(self.dec.flushed == self.dlv@.len());
                    assert(self.dec.out@.len() <= fo.len());
                }
            }
            if self.done {
                proof {
                    lemma_reaches(self.dec, b);
                    lemma_ring_basic(self.dec);
                    lemma_prefix_sub(self.dec.out@, self.dec.flushed as int);
                }
                if self.dec.pending() > 0 {
                    return (Result::NeedsMoreOutput, ip, op);
                }
                proof {
                    lemma_done_decodes(self.dec, b, self.dlv@);
                }
                return (Result::Success, ip, op);
            }
            let (st, ip2) = if self.tail.len() > 0 {
                self.tail_round(input, ip, Ghost(u0))
            } else {
                self.direct_round(input, ip, Ghost(u0))
            };
            ip = ip2;
            let ghost wk2 = self.work();
            proof {
                assert(round_work(s1, *self, (st, ip2), input@.len() as nat, ip0 as nat));
                assert(ip0 <= ip);
                lemma_kb(input@.len() - ip0, ip0 as int);
                lemma_kb(self.used@ - s1.used@, ip as int);
                lemma_kb(input@.len() as int, ip as int);
                if !self.bad {
                    assert(wk2 + 2 * s1.tl() <= wk1 + 8_000_000 * (ip - ip0) + (if st == Status::Yield { 0int } else { 2int })
                        + 2 * self.tl());
                    if st != Status::Short {
                        assert(self.tl() <= s1.tl());
                    }
                }
            }
            if st == Status::Bad || st == Status::Limit {
                assert(self.work() <= wk1 + 8_000_000 * (input@.len() - ip0) + xc() + 1);
                proof {
                    if cpl && self.limit@ {
                        let t = choose|t: spec::St| #[trigger] spec::reaches(b, t) && t.out.len() + 0x1_0000_0000
                            > MAX_OUT;
                        let k = choose|k: nat| spec::run(b, spec::init(), k) == spec::Step::Next(t);
                        lemma_on_way(b, k, t, fnn, fst);
                    }
                }
                return (Result::Error, ip, op);
            }
            proof {
                lemma_ring_basic(self.dec);
                assert(dec1.view() == dec0.view());
                if self.dec == dec1 {
                    assert(rk(b, self.dec.view()) == rk(b, dec0.view()));
                } else {
                    assert(rank_lt(b, self.dec.view(), dec0.view()));
                }
            }
            match st {
                Status::Done => {
                    let ghost sd = *self;
                    self.done = true;
                    assert(self.work() == sd.work()) by {
                        reveal(Stream::work);
                    }
                    assert(self.work() <= w0 + 8_000_002 * ip + 10 * op + 2);
                },
                Status::Short => {
                    if ip < input.len() {
                        proof {
                            assert(tl0 > 0);
                            assert(ip >= ip0);
                            assert(ip == ip0 ==> self.tail@.len() == 0);
                        }
                        continue;
                    }
                    op = self.flush_to(output, op, Ghost(d0));
                    proof {
                        lemma_reaches(self.dec, b);
                        lemma_ring_basic(self.dec);
                        lemma_prefix_sub(self.dec.out@, self.dec.flushed as int);
                        if cpl {
                            lemma_on_way(b, self.dec.steps@, self.dec.view(), fnn, fst);
                        }
                    }
                    if self.dec.pending() > 0 && op == output.len() {
                        return (Result::NeedsMoreOutput, ip, op);
                    }
                    return (Result::NeedsMoreInput, ip, op);
                },
                Status::Full => {
                    let ghost op1 = op;
                    let ghost wk3 = self.work();
                    let ghost fl1 = self.dec.flushed;
                    op = self.flush_to(output, op, Ghost(d0));
                    proof {
                        lemma_ring_basic(self.dec);
                    }
                    if self.dec.pending() > 0 {
                        proof {
                            lemma_reaches(self.dec, b);
                            lemma_ring_basic(self.dec);
                            lemma_prefix_sub(self.dec.out@, self.dec.flushed as int);
                            if cpl {
                                lemma_on_way(b, self.dec.steps@, self.dec.view(), fnn, fst);
                            }
                        }
                        return (Result::NeedsMoreOutput, ip, op);
                    }
                    proof {
                        assert(self.dec == dec1 ==> self.dec.flushed > dec0.flushed);
                        assert(self.dec.flushed > fl1);
                        assert(op > op1);
                        assert(self.work() == wk3 + 8 * (op - op1));
                    }
                },
                _ => {
                    proof {
                        assert(st == Status::Yield);
                        assert(self.work() <= w0 + 8_000_002 * ip + 10 * op);
                        assert(rank_lt(b, self.dec.view(), dec0.view()));
                    }
                },
            }
        }
    }

    /// Decodes from the bytes kept in `tail`, with up to `TAIL_STEP` more
    /// from `input[ip..]`. Returns why the decoder stopped and the new `ip`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(80)]
    fn tail_round(&mut self, input: &[u8], ip: usize, Ghost(u0): Ghost<nat>) -> (r: (Status, usize))
        requires
            old(self).inv(),
            !old(self).bad,
            !old(self).done,
            old(self).tail@.len() > 0,
            ip <= input@.len(),
            old(self).used@ == u0 + ip,
            u0 + input@.len() <= old(self).full@.len(),
            input@ == old(self).full@.subrange(u0 as int, (u0 + input@.len()) as int),
        ensures
            round_ok(*old(self), *final(self), r, input@.len(), u0),
            r.1 == ip ==> final(self).tail@.len() == 0 || ip == input@.len(),
            round_work(*old(self), *final(self), r, input@.len() as nat, ip as nat),
    {
        let ghost b = self.full@;
        let ghost o = *self;
        let ghost ip00 = ip;
        let mut ip = ip;
        let old_end = self.tail_base + self.tail.len() as u64;
        let mut add = input.len() - ip;
        if add > TAIL_STEP {
            add = TAIL_STEP;
        }
        append(&mut self.tail, input, ip, add);
        ip = ip + add;
        proof {
            self.used@ = (self.used@ + add) as nat;
            assert(input@.subrange(ip - add, ip as int) =~= b.subrange(u0 + ip - add, u0 + ip));
            assert(self.tail@ =~= b.subrange(self.tail_base as int, self.used@ as int));
        }
        let ghost r0 = self.dec;
        let ghost s1 = *self;
        let tracked mut wm = Meter { n: self.steps@ };
        let (st, g) = self.dec.run(self.tail.as_slice(), self.tail_base, BUDGET, Ghost(b), Tracked(&mut wm));
        proof {
            self.steps@ = wm.n;
            lemma_pot_lb(r0);
            lemma_ring_basic(r0);
            if st == Status::Bad {
                lemma_pot_lb(g@);
                lemma_ring_basic(g@);
            } else {
                lemma_pot_lb(self.dec);
                lemma_ring_basic(self.dec);
            }
        }
        if st == Status::Bad || st == Status::Limit {
            proof {
                if st == Status::Limit {
                    lemma_ring_basic(self.dec);
                    lemma_reaches(self.dec, b);
                    assert(self.dec.total + 0x1_0000_0000 > MAX_OUT);
                    assert(self.dec.view().out.len() == self.dec.total);
                    assert(spec::reaches(b, self.dec.view()));
                    assert(spec::reaches(self.full@, self.dec.view()) && self.dec.view().out.len() + 0x1_0000_0000 > MAX_OUT);
                }
            }
            let ghost fp = self.dec.pos as int;
            self.fail(st);
            proof {
                if st == Status::Bad {
                    lemma_work_bad(o, *self, g@, fp, input@.len() as int, ip00 as int);
                }
            }
            return (st, ip);
        }
        proof {
            lemma_ring_basic(r0);
            lemma_keep(r0.out@, self.dec.out@, r0.flushed as int);
        }
        let q = self.dec.pos / 8;
        let new_end = self.tail_base + self.tail.len() as u64;
        if q >= old_end {
            // Past the bytes kept: hand back the input after `q`.
            let back = (new_end - q) as usize;
            ip = ip - back;
            self.tail.clear();
            self.tail_base = 0;
            proof {
                self.used@ = q as nat;
            }
        } else {
            let drop = (q - self.tail_base) as usize;
            self.tail = drop_front(&self.tail, drop);
            self.tail_base = q;
            proof {
                assert(self.tail@ =~= b.subrange(self.tail_base as int, self.used@ as int));
            }
        }
        proof {
            lemma_ring_basic(self.dec);
            lemma_ring_basic(o.dec);
            lemma_work_diff(o, *self);
        }
        (st, ip)
    }

    /// Decodes straight from `input[ip..]`, which starts at the decoder's
    /// byte. Returns why the decoder stopped and the new `ip`.
    #[verifier::spinoff_prover]
    fn direct_round(&mut self, input: &[u8], ip: usize, Ghost(u0): Ghost<nat>) -> (r: (Status, usize))
        requires
            old(self).inv(),
            !old(self).bad,
            !old(self).done,
            old(self).tail@.len() == 0,
            ip <= input@.len(),
            old(self).used@ == u0 + ip,
            u0 + input@.len() <= old(self).full@.len(),
            input@ == old(self).full@.subrange(u0 as int, (u0 + input@.len()) as int),
        ensures
            round_ok(*old(self), *final(self), r, input@.len(), u0),
            r.0 == Status::Short ==> r.1 == input@.len(),
            r.0 != Status::Short && !final(self).bad ==> final(self).tail@.len() == 0,
            round_work(*old(self), *final(self), r, input@.len() as nat, ip as nat),
    {
        let ghost b = self.full@;
        let ghost o = *self;
        let ghost ip00 = ip;
        let mut ip = ip;
        let ilen = input.len();
        let q0 = self.dec.pos / 8;
        let rest = slice_from(input, ip);
        if self.dec.pos > 8 * (q0 + rest.len() as u64) {
            // A partly read byte the caller has not given again.
            return (Status::Short, ip);
        }
        proof {
            assert(rest@ =~= b.subrange(q0 as int, q0 + rest@.len()));
        }
        let ghost r0 = self.dec;
        let tracked mut wm = Meter { n: self.steps@ };
        let (st, g) = self.dec.run(rest, q0, BUDGET, Ghost(b), Tracked(&mut wm));
        proof {
            self.steps@ = wm.n;
            lemma_pot_lb(r0);
            lemma_ring_basic(r0);
            if st == Status::Bad {
                lemma_pot_lb(g@);
                lemma_ring_basic(g@);
            } else {
                lemma_pot_lb(self.dec);
                lemma_ring_basic(self.dec);
            }
        }
        if st == Status::Bad || st == Status::Limit {
            proof {
                if st == Status::Limit {
                    lemma_ring_basic(self.dec);
                    lemma_reaches(self.dec, b);
                    assert(self.dec.total + 0x1_0000_0000 > MAX_OUT);
                    assert(self.dec.view().out.len() == self.dec.total);
                    assert(spec::reaches(b, self.dec.view()));
                    assert(spec::reaches(self.full@, self.dec.view()) && self.dec.view().out.len() + 0x1_0000_0000 > MAX_OUT);
                }
            }
            let ghost fp = self.dec.pos as int;
            self.fail(st);
            proof {
                if st == Status::Bad {
                    assert(q0 == o.used@);
                    lemma_work_bad(o, *self, g@, fp, input@.len() as int, ip00 as int);
                }
            }
            return (st, ip);
        }
        proof {
            lemma_ring_basic(r0);
            lemma_keep(r0.out@, self.dec.out@, r0.flushed as int);
        }
        let q = self.dec.pos / 8;
        proof {
            assert(self.dec.pos <= 8 * (q0 + rest@.len()));
            assert(q <= q0 + rest@.len());
            assert(rest@.len() == input@.len() - ip);
        }
        ip = ip + (q - q0) as usize;
        proof {
            self.used@ = q as nat;
        }
        if st == Status::Short && ip < input.len() {
            // Keep the rest of the input, from the item's start.
            let ghost before = ip;
            self.tail_base = q;
            append(&mut self.tail, input, ip, input.len() - ip);
            ip = input.len();
            proof {
                self.used@ = (u0 + ip) as nat;
                assert(input@.subrange(before as int, ip as int) =~= b.subrange(u0 + before, u0 + ip));
                assert(self.tail@ =~= b.subrange(self.tail_base as int, self.used@ as int));
            }
        }
        proof {
            lemma_ring_basic(self.dec);
            lemma_ring_basic(o.dec);
            lemma_work_diff(o, *self);
        }
        (st, ip)
    }

    /// Hands out decoded bytes to `output[op..]`; returns the new `op`.
    #[verifier::spinoff_prover]
    fn flush_to(&mut self, output: &mut [u8], op: usize, Ghost(d0): Ghost<Seq<u8>>) -> (r: usize)
        requires
            old(self).inv(),
            !old(self).bad,
            op <= old(output)@.len(),
            old(self).dlv@ == d0 + old(output)@.subrange(0, op as int),
        ensures
            final(self).inv(),
            *final(self) == (Stream { dec: final(self).dec, dlv: final(self).dlv, ..*old(self) }),
            final(self).dec.view() == old(self).dec.view(),
            final(self).dec.steps == old(self).dec.steps,
            final(self).dec.flushed >= old(self).dec.flushed,
            final(self).dec.total == old(self).dec.total,
            op <= r <= old(output)@.len(),
            final(output)@.len() == old(output)@.len(),
            final(self).dlv@ == d0 + final(output)@.subrange(0, r as int),
            r < old(output)@.len() ==> final(self).dec.total == final(self).dec.flushed,
            final(self).work() == old(self).work() + lbyte() * (r - op),
            final(self).dec.flushed == old(self).dec.flushed + (r - op),
    {
        let ghost f0 = self.dec;
        let ghost o0 = output@;
        let olen = output.len();
        let n = self.dec.flush(output, op);
        proof {
            assert(n == f0.total - f0.flushed || n == o0.len() - op);
            assert(n <= o0.len() - op);
            lemma_ring_basic(f0);
            let fl = f0.flushed as int;
            assert(output@.subrange(0, op as int) == o0.subrange(0, op as int));
            assert(output@.subrange(0, (op + n) as int) =~= output@.subrange(0, op as int) + f0.out@.subrange(fl, fl + n));
            assert(self.dec.out@.subrange(0, self.dec.flushed as int) =~= f0.out@.subrange(0, fl) + f0.out@.subrange(fl, fl + n));
            self.dlv@ = self.dlv@ + f0.out@.subrange(fl, fl + n);
            assert(self.dlv@ =~= d0 + output@.subrange(0, (op + n) as int));
            lemma_ring_basic(self.dec);
        }
        op + n
    }

    /// The decoder stopped with `Bad` or `Limit`.
    #[verifier::spinoff_prover]
    fn fail(&mut self, st: Status)
        requires
            st == Status::Bad || st == Status::Limit,
            st == Status::Bad ==> spec::rejects(old(self).full@),
            st == Status::Limit ==> exists|t: spec::St| #[trigger] spec::reaches(old(self).full@, t) && t.out.len()
                + 0x1_0000_0000 > MAX_OUT,
            old(self).full@.len() <= MAX_INPUT,
            old(self).used@ <= old(self).full@.len(),
        ensures
            final(self).inv(),
            final(self).bad,
            final(self).full == old(self).full,
            final(self).used == old(self).used,
            final(self).dlv == old(self).dlv,
            final(self).done == old(self).done,
            final(self).steps == old(self).steps,
            final(self).tail == old(self).tail,
    {
        self.bad = true;
        proof {
            self.limit@ = st == Status::Limit;
        }
    }
}

/// `kbit()` written out, for linear arithmetic.
pub proof fn lemma_kb(x: int, y: int)
    ensures
        8 * kbit() * x == 8_000_000 * x,
        (8 * kbit() + 2) * y == 8_000_002 * y,
{
    assert(8 * kbit() * x == 8_000_000 * x && (8 * kbit() + 2) * y == 8_000_002 * y) by (nonlinear_arith)
        requires
            kbit() == 1_000_000,
    ;
}

/// How the work changes when the decoder goes from `o.dec` to `n.dec`
/// without handing anything out: the steps taken, less what the decoder
/// earned, plus the bits of the input taken and a round for bytes kept.
pub proof fn lemma_work_diff(o: Stream, n: Stream)
    requires
        !o.bad,
        !n.bad,
        o.dec.flushed == n.dec.flushed,
        o.dec.total == o.dec.out@.len(),
        n.dec.total == n.dec.out@.len(),
    ensures
        n.work() - o.work() == (n.steps@ - o.steps@) - earned(o.dec, n.dec) + 8 * kbit() * (n.used@ - o.used@) + 2 * (
        n.tl() - o.tl()),
{
    let k = kbit();
    let (nu, ou, np, op) = (n.used@ as int, o.used@ as int, n.dec.pos as int, o.dec.pos as int);
    assert(k * (8 * nu + 8 - np) - k * (8 * ou + 8 - op) == 8 * k * (nu - ou) - k * (np - op)) by (nonlinear_arith);
    let (nt, ot, f) = (n.dec.total as int, o.dec.total as int, o.dec.flushed as int);
    assert(lbyte() * (rmax() - (nt - f)) - lbyte() * (rmax() - (ot - f)) == -(lbyte() * (nt - ot))) by (nonlinear_arith);
}

/// A round that found the stream malformed, at `g` the last good state,
/// having read up to bit `fp`: its work is paid for by the credit and the
/// bits of the input it was given.
pub proof fn lemma_work_bad(o: Stream, n: Stream, g: Decoder, fp: int, ilen: int, ip: int)
    requires
        o.inv(),
        !o.bad,
        n.bad,
        g.wf(),
        g.flushed == o.dec.flushed,
        o.dec.pos <= g.pos <= fp,
        fp <= 8 * (o.used@ + ilen - ip),
        ip <= ilen,
        n.steps@ <= o.steps@ + earned(o.dec, g) + xc() + 1 + kbit() * (fp - g.pos),
    ensures
        n.work() <= o.work() + 8 * kbit() * (ilen - ip) + xc() + 1,
{
    lemma_pot_lb(g);
    lemma_ring_basic(g);
    lemma_ring_basic(o.dec);
    lemma_pot_lb(o.dec);
}

/// `reached` is `spec::reaches`.
#[verifier::spinoff_prover]
pub proof fn lemma_reaches(d: Decoder, b: Seq<u8>)
    requires
        d.reached(b),
    ensures
        spec::reaches(b, d.view()),
{
}

#[verifier::spinoff_prover]
pub proof fn lemma_prefix_sub(s: Seq<u8>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        s.subrange(0, n).is_prefix_of(s),
{
    assert(s.subrange(0, n) =~= s.subrange(0, s.subrange(0, n).len() as int));
}

#[verifier::spinoff_prover]
pub proof fn lemma_keep(a: Seq<u8>, b: Seq<u8>, k: int)
    requires
        a.is_prefix_of(b),
        0 <= k <= a.len(),
    ensures
        b.subrange(0, k) == a.subrange(0, k),
{
    assert(b.subrange(0, k) =~= a.subrange(0, k)) by {
        assert forall|i: int| 0 <= i < k implies b[i] == a[i] by {
            assert(a[i] == b.subrange(0, a.len() as int)[i]);
        }
    }
}

/// A finished decoder, with everything handed out, decodes `b`.
#[verifier::spinoff_prover]
pub proof fn lemma_done_decodes(d: Decoder, b: Seq<u8>, dlv: Seq<u8>)
    requires
        d.wf(),
        d.reached(b),
        d.ph == Ph::Done,
        d.flushed == d.total,
        dlv == d.out@.subrange(0, d.flushed as int),
    ensures
        spec::decodes(b, dlv, (d.pos / 8) as int),
{
    lemma_ring_basic(d);
    assert(dlv =~= d.view().out);
    assert(spec::reaches(b, d.view()));
    assert(8 * (d.pos / 8) == d.pos);
}

/// Appends `src[at..at + n]` to `v`.
#[verifier::spinoff_prover]
fn append(v: &mut Vec<u8>, src: &[u8], at: usize, n: usize)
    requires
        at + n <= src@.len(),
    ensures
        final(v)@ == old(v)@ + src@.subrange(at as int, at + n),
{
    let ghost v0 = v@;
    let len = src.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            len == src@.len(),
            at + n <= src@.len(),
            v@ == v0 + src@.subrange(at as int, at + i),
        decreases n - i,
    {
        v.push(src[at + i]);
        i = i + 1;
        proof {
            assert(src@.subrange(at as int, at + i) =~= src@.subrange(at as int, at + i - 1).push(src@[at + i - 1]));
            assert(v@ =~= v0 + src@.subrange(at as int, at + i));
        }
    }
    proof {
        assert(v@ =~= v0 + src@.subrange(at as int, at + n));
    }
}

/// `v[k..]`, as a new vector.
#[verifier::spinoff_prover]
fn drop_front(v: &Vec<u8>, k: usize) -> (r: Vec<u8>)
    requires
        k <= v@.len(),
    ensures
        r@ == v@.subrange(k as int, v@.len() as int),
{
    let mut r: Vec<u8> = Vec::new();
    let mut i = k;
    while i < v.len()
        invariant
            k <= i <= v@.len(),
            r@ == v@.subrange(k as int, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof {
            assert(v@.subrange(k as int, i as int) =~= v@.subrange(k as int, i - 1).push(v@[i - 1]));
        }
    }
    r
}

/// `&s[a..]`.
fn slice_from<'a>(s: &'a [u8], a: usize) -> (r: &'a [u8])
    requires
        a <= s@.len(),
    ensures
        r@ == s@.subrange(a as int, s@.len() as int),
{
    &s[a..]
}

} // verus!
