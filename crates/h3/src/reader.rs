//! The stream reader: an HTTP/3 stream's bytes in, its frames out, as they
//! arrive and however they are split.
use crate::frame::*;
use crate::lemmas::*;
use crate::spec::*;
use crate::varint::*;
use verilith_core::prims::extend;
use vstd::prelude::*;

verus! {

/// Where a field section is: `Input(a, b)` is `input[a..b]` of the call that
/// returned it, `Buf(off)` is `reader.buffered()[off..]`. Either is valid
/// until the next call.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Src {
    Input(usize, usize),
    Buf(usize),
}

/// What `Reader::next` reports. Each call returns one event and the number
/// of input bytes it used; call again with the rest.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Event {
    /// All the input was used; more is needed.
    Need,
    /// The stream ended (`fin`) and was well formed.
    End,
    /// The stream is in error, with this HTTP/3 error code. Every later
    /// call returns the same.
    Error(u64),
    /// The stream is not HTTP/3 framed from here on (a QPACK stream, or an
    /// unknown type, reported by the `StreamType` before this): the rest of
    /// the stream is the caller's. `used` is 0.
    Handoff,
    /// A unidirectional stream's type.
    StreamType(u64),
    /// A push stream's push ID.
    PushId(u64),
    /// `input[a..b]` is DATA payload (content).
    Data(usize, usize),
    /// A HEADERS frame's encoded field section.
    Headers(Src),
    /// A PUSH_PROMISE: its push ID and encoded field section.
    PushPromise(u64, Src),
    Settings(Settings),
    CancelPush(u64),
    Goaway(u64),
    MaxPushId(u64),
}

pub open spec fn src_view(s: Src, input: Seq<u8>, buf: Seq<u8>) -> Seq<u8> {
    match s {
        Src::Input(a, b) => input.subrange(a as int, b as int),
        Src::Buf(off) => buf.skip(off as int),
    }
}

pub open spec fn src_ok(s: Src, input: Seq<u8>, buf: Seq<u8>, used: nat) -> bool {
    match s {
        Src::Input(a, b) => a <= b <= used,
        Src::Buf(off) => off <= buf.len(),
    }
}

/// Whether `e` is one of the events in `spec::Ev`.
pub open spec fn logged(e: Event) -> bool {
    !(e is Need || e is End || e is Error || e is Handoff || e is Data)
}

pub open spec fn ev_view(e: Event, input: Seq<u8>, buf: Seq<u8>) -> Ev {
    match e {
        Event::StreamType(t) => Ev::StreamType(t),
        Event::PushId(t) => Ev::PushId(t),
        Event::Headers(s) => Ev::Headers(src_view(s, input, buf)),
        Event::PushPromise(id, s) => Ev::PushPromise(id, src_view(s, input, buf)),
        Event::Settings(s) => Ev::Settings(s),
        Event::CancelPush(v) => Ev::CancelPush(v),
        Event::Goaway(v) => Ev::Goaway(v),
        Event::MaxPushId(v) => Ev::MaxPushId(v),
        _ => Ev::StreamType(0),
    }
}

pub open spec fn ev_ok(e: Event, input: Seq<u8>, buf: Seq<u8>, used: nat) -> bool {
    match e {
        Event::Headers(s) | Event::PushPromise(_, s) => src_ok(s, input, buf, used),
        _ => true,
    }
}

#[derive(Clone, Copy)]
enum Mode {
    /// Between units, with the first `hn` bytes of the next in `buf`.
    Unit,
    /// Inside a frame's payload.
    Payload,
    Failed(u64),
    Handoff,
    Ended,
}

/// The reader of one HTTP/3 stream.
pub struct Reader {
    server: bool,
    limit: u64,
    mode: Mode,
    /// In `Unit` mode, the state at the next unit; in `Payload` mode, the
    /// state after the frame's header was accepted.
    st: RSt,
    buf: Vec<u8>,
    hn: usize,
    kind: Kind,
    rem: u64,
    uni: Ghost<bool>,
    seen: Ghost<Seq<u8>>,
    q: Ghost<nat>,
    st0: Ghost<RSt>,
    ty: Ghost<nat>,
    flen: Ghost<nat>,
    hlen: Ghost<nat>,
    events: Ghost<Seq<Ev>>,
    body: Ghost<Seq<u8>>,
}

/// How a call went on, inside `next`.
enum Step {
    Ret(Event, usize),
    Cont(usize),
    Stop,
}

impl Reader {
    /// Everything the reader has been given and used.
    pub closed spec fn seen(&self) -> Seq<u8> {
        self.seen@
    }

    /// The events it has reported (`spec::Ev`), in order.
    pub closed spec fn events(&self) -> Seq<Ev> {
        self.events@
    }

    /// The DATA payload bytes it has reported.
    pub closed spec fn body(&self) -> Seq<u8> {
        self.body@
    }

    pub closed spec fn is_server(&self) -> bool {
        self.server
    }

    pub closed spec fn lim(&self) -> nat {
        self.limit as nat
    }

    pub closed spec fn st_start(&self) -> RSt {
        start(self.uni@, self.server)
    }

    pub closed spec fn buf_v(&self) -> Seq<u8> {
        self.buf@
    }

    /// Whether the stream can still be read (it has not failed, ended or
    /// been handed off).
    pub closed spec fn live(&self) -> bool {
        self.mode is Unit || self.mode is Payload
    }

    /// The DATA reported so far is all of the stream's content so far.
    pub proof fn lemma_content(&self)
        requires
            self.wf(),
            self.live(),
        ensures
            self.body() == content(self.is_server(), self.lim(), self.seen(), self.st_start()),
            self.events() == self.spec_out().ev,
    {
        let srv = self.server;
        let lim = self.limit as nat;
        let s = self.seen@;
        let q = self.q@;
        let b = s.take(q as int);
        let w = s.skip(q as int);
        let stt = start(self.uni@, self.server);
        assert(b + w =~= s);
        if self.mode is Unit {
            assert(unit(srv, lim, w, self.st) is Incomplete);
            lemma_stay(srv, lim, b, w, stt, self.st);
            assert(self.body@ + seq![] =~= self.body@);
        } else {
            lemma_hdr_ok(w);
            assert(unit(srv, lim, w, self.st0@) is Incomplete);
            lemma_stay(srv, lim, b, w, stt, self.st0@);
        }
    }

    /// What the stream so far means, by the spec.
    pub open spec fn spec_out(&self) -> Out {
        run(self.is_server(), self.lim(), self.seen(), self.st_start())
    }

    /// The potential of the work bound: two steps per buffered payload
    /// byte.
    pub closed spec fn pot(&self) -> nat {
        if self.mode is Payload && buffered(self.kind) {
            2 * self.buf@.len()
        } else {
            0
        }
    }

    /// The reader's invariant.
    pub closed spec fn wf(&self) -> bool {
        let srv = self.server;
        let lim = self.limit as nat;
        let s = self.seen@;
        let q = self.q@;
        let b = s.take(q as int);
        let w = s.skip(q as int);
        let r = run(srv, lim, b, start(self.uni@, srv));
        &&& q <= s.len()
        &&& self.events@ == run(srv, lim, s, start(self.uni@, srv)).ev
        &&& match self.mode {
            Mode::Unit => {
                &&& r == (Out { ev: self.events@, body: self.body@, tail: Tail::At(self.st, q) })
                &&& self.hn == w.len()
                &&& self.hn <= self.buf@.len()
                &&& self.buf@.take(self.hn as int) == w
                &&& match self.st {
                    RSt::Frames(_) => hdr_dec(w) is Short,
                    _ => var_dec(w) is Short,
                }
            },
            Mode::Payload => {
                let h = self.hlen@;
                let len = self.flen@;
                &&& r.ev == self.events@
                &&& r.tail == Tail::At(self.st0@, q)
                &&& self.st0@ is Frames
                &&& hdr_dec(w) == Hdr::Ok(self.ty@, len, h)
                &&& accept(self.st0@->Frames_0, srv, lim, self.ty@, len) == Ok(self.st->Frames_0)
                &&& self.st is Frames
                &&& self.kind == kind(self.ty@)
                &&& !(self.kind is H2)
                &&& h <= w.len() < h + len
                &&& self.rem as nat == h + len - w.len()
                &&& (buffered(self.kind) ==> self.buf@ == w.skip(h as int))
                &&& self.body@ == r.body + (if self.kind == Kind::Data { w.skip(h as int) } else { seq![] })
            },
            Mode::Failed(e) => run(srv, lim, s, start(self.uni@, srv)).tail == Tail::Fail(e) || (run(srv, lim, s, start(self.uni@, srv)).tail is At && end_of(srv, lim, s, start(self.uni@, srv)) == Err::<(), u64>(e)),
            Mode::Handoff => run(srv, lim, s, start(self.uni@, srv)).tail == Tail::Handoff(run(srv, lim, s, start(self.uni@, srv)).tail->Handoff_0, s.len()),
            Mode::Ended => end_of(srv, lim, s, start(self.uni@, srv)) == Ok::<(), u64>(()),
        }
    }

    /// A reader for a unidirectional stream (it starts with the stream
    /// type) received by a server (`server`) or a client. `limit` bounds
    /// the HEADERS, PUSH_PROMISE and SETTINGS payloads it buffers.
    pub fn new_uni(server: bool, limit: u64) -> (r: Reader)
        ensures
            r.wf(),
            r.seen() == Seq::<u8>::empty(),
            r.events() == Seq::<Ev>::empty(),
            r.body() == Seq::<u8>::empty(),
            r.is_server() == server,
            r.lim() == limit,
            r.st_start() == start(true, server),
            r.pot() == 0,
    {
        Self::make(true, server, limit, RSt::Type)
    }

    /// A reader for a request stream: at a server (`server`), the request;
    /// at a client, the response.
    pub fn new_request(server: bool, limit: u64) -> (r: Reader)
        ensures
            r.wf(),
            r.seen() == Seq::<u8>::empty(),
            r.events() == Seq::<Ev>::empty(),
            r.body() == Seq::<u8>::empty(),
            r.is_server() == server,
            r.lim() == limit,
            r.st_start() == start(false, server),
            r.pot() == 0,
    {
        let st = if server {
            RSt::Frames(Order::Request(Phase::Start))
        } else {
            RSt::Frames(Order::Response(Phase::Start))
        };
        Self::make(false, server, limit, st)
    }

    fn make(uni: bool, server: bool, limit: u64, st: RSt) -> (r: Reader)
        requires
            st == start(uni, server),
        ensures
            r.wf(),
            r.seen() == Seq::<u8>::empty(),
            r.events() == Seq::<Ev>::empty(),
            r.body() == Seq::<u8>::empty(),
            r.is_server() == server,
            r.lim() == limit,
            r.st_start() == start(uni, server),
            r.pot() == 0,
    {
        let r = Reader {
            server,
            limit,
            mode: Mode::Unit,
            st,
            buf: Vec::new(),
            hn: 0,
            kind: Kind::Other,
            rem: 0,
            uni: Ghost(uni),
            seen: Ghost(Seq::empty()),
            q: Ghost(0),
            st0: Ghost(st),
            ty: Ghost(0),
            flen: Ghost(0),
            hlen: Ghost(0),
            events: Ghost(Seq::empty()),
            body: Ghost(Seq::empty()),
        };
        proof {
            lemma_unit_empty(server, limit as nat, st);
            assert(Seq::<u8>::empty().take(0) =~= Seq::<u8>::empty());
            assert(Seq::<u8>::empty().skip(0) =~= Seq::<u8>::empty());
            assert(r.buf@.take(0) =~= Seq::<u8>::empty());
        }
        r
    }

    /// The buffer `Src::Buf` offsets point into.
    pub fn buffered(&self) -> (r: &[u8])
        ensures
            r@ == self.buf_v(),
    {
        self.buf.as_slice()
    }

    /// Reads on: `input` is the next bytes of the stream, and `fin` says
    /// whether they are its last. Returns one event and how many bytes of
    /// `input` it used. Never panics; see `next_metered` for what it
    /// guarantees.
    #[inline]
    pub fn next(&mut self, input: &[u8], fin: bool) -> (r: (Event, usize))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            next_ok(*old(self), *final(self), input@, fin, r.0, r.1 as nat),
    {
        let (e, u, _) = self.next_metered(input, fin);
        (e, u)
    }

    /// `next`, with its work: the ghost result counts loop turns and bytes
    /// copied. Over any sequence of calls the potential (`pot`) starts at 0
    /// and stays nonnegative, so the total is at most 4 per input byte plus
    /// 64 per call.
    #[inline(always)]
    pub fn next_metered(&mut self, input: &[u8], fin: bool) -> (r: (Event, usize, Ghost<nat>))
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            next_ok(*old(self), *final(self), input@, fin, r.0, r.1 as nat),
            r.2@ + final(self).pot() <= old(self).pot() + 4 * r.1 + 64,
    {
        hide(run);
        hide(unit);
        hide(end_of);
        match self.mode {
            Mode::Failed(e) => {
                proof {
                    assert(input@.take(0) =~= Seq::<u8>::empty());
                    assert(self.seen@ + input@.take(0) =~= self.seen@);
                }
                return (Event::Error(e), 0, Ghost(1));
            },
            Mode::Handoff => {
                proof {
                    assert(input@.take(0) =~= Seq::<u8>::empty());
                    assert(self.seen@ + input@.take(0) =~= self.seen@);
                }
                return (Event::Handoff, 0, Ghost(1));
            },
            Mode::Ended => {
                proof {
                    assert(input@.take(0) =~= Seq::<u8>::empty());
                    assert(self.seen@ + input@.take(0) =~= self.seen@);
                }
                return (Event::End, 0, Ghost(1));
            },
            _ => {},
        }
        let ghost o = *self;
        assert(o == *old(self));
        let mut pos: usize = 0;
        let ghost mut steps: nat = 0;
        if matches!(self.mode, Mode::Payload) {
            match self.resume(input, Ghost(o), fin) {
                (Step::Ret(e, u), g) => return (e, u, g),
                (Step::Cont(p), g) => {
                    pos = p;
                    proof {
                        steps = g@;
                    }
                },
                (Step::Stop, g) => {
                    return self.finish(input, fin, Ghost(o), g);
                },
            }
        } else if self.hn > 0 {
            match self.window(input, Ghost(o), fin) {
                (Step::Ret(e, u), g) => return (e, u, g),
                (Step::Cont(p), g) => {
                    pos = p;
                    proof {
                        steps = g@;
                    }
                },
                (Step::Stop, g) => {
                    return self.finish(input, fin, Ghost(o), g);
                },
            }
        }
        let len = input.len();
        while pos < len
            invariant
                self.wf(),
                pos <= len,
                len == input@.len(),
                self.mode is Unit,
                self.hn == 0,
                same_cfg(o, *self),
                o == *old(self),
                self.seen@ == o.seen@ + input@.take(pos as int),
                self.events@ == o.events@,
                self.body@ == o.body@,
                steps + 1 <= o.pot() + 4 * pos + 32,
            decreases len - pos,
        {
            proof {
                steps = steps + 1;
            }
            match self.st {
                RSt::Frames(_) => {
                    match read_hdr(input, pos) {
                        None => {
                            let r = self.short(input, pos, fin, Ghost(o), Ghost(steps));
                            assert(next_ok(o, *self, input@, fin, r.0, r.1 as nat));
                            assert(o == *old(self));
                            return r;
                        },
                        Some((t, flen, e)) => {
                            let ghost h = (e - pos) as nat;
                            proof {
                                lemma_cut(o.seen@, input@, pos as int, e as int);
                                lemma_hdr_ok(input@.skip(pos as int));
                                lemma_hdr_same(input@.skip(pos as int), input@.subrange(pos as int, e as int), h);
                                assert(self.seen@.skip(self.q@ as int).len() == 0);
                                assert(self.seen@.take(self.q@ as int) =~= self.seen@);
                            }
                            self.seen = Ghost(o.seen@ + input@.take(e as int));
                            match self.on_hdr(input, e, t, flen, Ghost(h), Ghost(o), Ghost(steps), fin) {
                                (Step::Ret(ev, u), g) => return (ev, u, g),
                                (Step::Cont(p), g) => {
                                    pos = p;
                                    proof {
                                        steps = g@;
                                    }
                                },
                                (Step::Stop, g) => {
                                    return self.finish(input, fin, Ghost(o), g);
                                },
                            }
                        },
                    }
                },
                _ => {
                    match read_var(input, pos) {
                        None => {
                            let r = self.short(input, pos, fin, Ghost(o), Ghost(steps));
                            assert(next_ok(o, *self, input@, fin, r.0, r.1 as nat));
                            assert(o == *old(self));
                            return r;
                        },
                        Some((v, e)) => {
                            proof {
                                lemma_cut(o.seen@, input@, pos as int, e as int);
                                lemma_var_bound(input@.skip(pos as int));
                                lemma_var_same(input@.skip(pos as int), input@.subrange(pos as int, e as int), (e - pos) as nat);
                                assert(self.seen@.skip(self.q@ as int).len() == 0);
                                assert(self.seen@.take(self.q@ as int) =~= self.seen@);
                            }
                            self.seen = Ghost(o.seen@ + input@.take(e as int));
                            let r = self.on_var(input, e, v, Ghost(o), Ghost(steps), fin);
                            assert(next_ok(o, *self, input@, fin, r.0, r.1 as nat));
                            return r;
                        },
                    }
                },
            }
        }
        proof {
            assert(input@.take(pos as int) =~= input@);
        }
        self.finish(input, fin, Ghost(o), Ghost(steps))
    }
}


/// `b[i..j]`.
#[inline(always)]
fn sub(b: &[u8], i: usize, j: usize) -> (r: &[u8])
    requires
        i <= j <= b@.len(),
    ensures
        r@ == b@.subrange(i as int, j as int),
{
    &b[i..j]
}

proof fn lemma_cut(a: Seq<u8>, input: Seq<u8>, pos: int, e: int)
    requires
        0 <= pos <= e <= input.len(),
    ensures
        (a + input.take(e)).take(a.len() + pos) == a + input.take(pos),
        (a + input.take(e)).skip(a.len() + pos) == input.subrange(pos, e),
        input.subrange(pos, e) == input.skip(pos).take(e - pos),
        (a + input.take(e)).len() == a.len() + e,
{
    assert((a + input.take(e)).take(a.len() + pos) =~= a + input.take(pos));
    assert((a + input.take(e)).skip(a.len() + pos) =~= input.subrange(pos, e));
    assert(input.subrange(pos, e) =~= input.skip(pos).take(e - pos));
}

/// A header (or a varint) that is still short is less than 16 (8) bytes.
proof fn lemma_short_len(w: Seq<u8>)
    ensures
        hdr_dec(w) is Short ==> w.len() < 16,
        var_dec(w) is Short ==> w.len() < 8,
{
    if w.len() >= 8 {
        assert(var_dec(w) is Ok);
        if w.len() >= 16 {
            let n = var_dec(w)->Ok_1;
            lemma_var_bound(w);
            assert(var_dec(w.skip(n as int)) is Ok);
        }
    }
}

/// The event for a completed buffered frame whose payload is `input[a..b]`
/// (`inp`) or the whole buffer.
#[inline(always)]
fn mk_event(c: CEv, inp: bool, a: usize, b: usize, Ghost(input): Ghost<Seq<u8>>, Ghost(buf): Ghost<Seq<u8>>) -> (r: Event)
    requires
        inp ==> a <= b <= input.len(),
        !inp ==> a == 0 && b == buf.len(),
        c matches CEv::PushPromise(_, off) ==> off <= b - a,
    ensures
        logged(r),
        ev_view(r, input, buf) == cev_view(c, if inp { input.subrange(a as int, b as int) } else { buf }),
        ev_ok(r, input, buf, b as nat),
        !inp ==> forall|u: nat| #[trigger] ev_ok(r, input, buf, u),
{
    let src = if inp {
        Src::Input(a, b)
    } else {
        Src::Buf(0)
    };
    proof {
        assert(buf.skip(0) =~= buf);
    }
    match c {
        CEv::Headers => Event::Headers(src),
        CEv::PushPromise(id, off) => {
            let s2 = if inp {
                Src::Input(a + off, b)
            } else {
                Src::Buf(off)
            };
            proof {
                if inp {
                    assert(input.subrange(a + off, b as int) =~= input.subrange(a as int, b as int).skip(off as int));
                }
            }
            Event::PushPromise(id, s2)
        },
        CEv::Settings(x) => Event::Settings(x),
        CEv::CancelPush(v) => Event::CancelPush(v),
        CEv::Goaway(v) => Event::Goaway(v),
        CEv::MaxPushId(v) => Event::MaxPushId(v),
    }
}

/// What a step of `next` guarantees (see `next_ok`); `lo` is a lower
/// bound on the bytes it used.
spec fn step_ok(o: Reader, n: Reader, input: Seq<u8>, fin: bool, s: Step, g: nat, lo: nat) -> bool {
    match s {
        Step::Ret(e, u) => n.wf() && next_ok(o, n, input, fin, e, u as nat) && g + n.pot() <= o.pot() + 4 * u + 64 && u >= lo,
        Step::Cont(p) => {
            &&& n.wf()
            &&& n.mode is Unit
            &&& n.hn == 0
            &&& same_cfg(o, n)
            &&& lo <= p <= input.len()
            &&& n.seen@ == o.seen@ + input.take(p as int)
            &&& n.events@ == o.events@
            &&& n.body@ == o.body@
            &&& g + 1 <= o.pot() + 4 * p + 32
        },
        Step::Stop => {
            &&& n.wf()
            &&& (n.mode is Unit || n.mode is Payload)
            &&& same_cfg(o, n)
            &&& n.seen@ == o.seen@ + input
            &&& n.events@ == o.events@
            &&& n.body@ == o.body@
            &&& g + n.pot() + 1 <= o.pot() + 4 * input.len() + 64
        },
    }
}

/// The state inside a call once a unit's first bytes (a header or a
/// varint) are in `seen`, before it is handled.
spec fn pre(n: Reader, o: Reader, input: Seq<u8>, e: nat) -> bool {
    let q = n.q@;
    &&& n.mode is Unit
    &&& same_cfg(o, n)
    &&& n.events@ == o.events@
    &&& n.body@ == o.body@
    &&& q <= n.seen@.len()
    &&& run(n.server, n.limit as nat, n.seen@.take(q as int), start(n.uni@, n.server)) == (Out { ev: n.events@, body: n.body@, tail: Tail::At(n.st, q) })
    &&& e <= input.len()
    &&& n.seen@ == o.seen@ + input.take(e as int)
    &&& n.uni@ == o.uni@
}

impl Reader {
    /// A frame header has been read: `t`, `flen`, and `h` bytes, the last of
    /// them `input[..e]`.
    #[verifier::rlimit(80)]
    #[inline(always)]
    fn on_hdr(&mut self, input: &[u8], e: usize, t: u64, flen: u64, Ghost(h): Ghost<nat>, Ghost(o): Ghost<Reader>, Ghost(steps): Ghost<nat>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            pre(*old(self), o, input@, e as nat),
            old(self).st is Frames,
            hdr_dec(old(self).seen@.skip(old(self).q@ as int)) == Hdr::Ok(t as nat, flen as nat, h),
            old(self).q@ + h == old(self).seen@.len(),
            steps + 1 <= o.pot() + 4 * e + 32,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, e as nat),
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost st = self.st;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost stt = start(self.uni@, self.server);
        let o0 = match self.st {
            RSt::Frames(x) => x,
            _ => Order::Request(Phase::Start),
        };
        proof {
            assert(b + w =~= s);
            lemma_hdr_ok(w);
        }
        match accept_x(o0, self.server, self.limit, t, flen) {
            Err(err) => {
                self.mode = Mode::Failed(err);
                proof {
                    assert(unit(srv, lim, w, st) == Unit::Fail(err)) by {
                        reveal(unit);
                    }
                    lemma_fail(srv, lim, b, w, stt, st);
                }
                return (Step::Ret(Event::Error(err), e), Ghost((steps + 1) as nat));
            },
            Ok(o2) => {
                let k = kind_of(t);
                let len = input.len();
                let avail = len - e;
                if flen <= avail as u64 {
                    self.whole(input, e, t, flen, o2, Ghost(h), Ghost(o), Ghost(steps), fin)
                } else {
                    self.part(input, e, t, flen, o2, Ghost(h), Ghost(o), Ghost(steps), fin)
                }
            },
        }
    }

    /// A frame whose payload is all in `input`.
    #[verifier::rlimit(80)]
    #[inline(always)]
    fn whole(&mut self, input: &[u8], e: usize, t: u64, flen: u64, o2: Order, Ghost(h): Ghost<nat>, Ghost(o): Ghost<Reader>, Ghost(steps): Ghost<nat>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            pre(*old(self), o, input@, e as nat),
            old(self).st is Frames,
            hdr_dec(old(self).seen@.skip(old(self).q@ as int)) == Hdr::Ok(t as nat, flen as nat, h),
            old(self).q@ + h == old(self).seen@.len(),
            accept(old(self).st->Frames_0, old(self).server, old(self).limit as nat, t as nat, flen as nat) == Ok::<Order, u64>(o2),
            steps + 1 <= o.pot() + 4 * e + 32,
            flen <= input@.len() - e,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, e as nat),
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost st = self.st;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost stt = start(self.uni@, self.server);
        let k = kind_of(t);
        let len = input.len();
        let avail = len - e;
        proof {
            assert(b + w =~= s);
            lemma_hdr_ok(w);
        }
        let end = e + flen as usize;
        let ghost s2 = o.seen@ + input@.take(end as int);
        let ghost w2 = s2.skip(q as int);
        proof {
            assert(s2.take(q as int) =~= b);
            assert(w2.take(h as int) =~= w);
            assert(w2.len() == h + flen);
            assert(w2.take(h as int) =~= w.take(h as int));
            lemma_hdr_same(w, w2, h);
            assert(w2.subrange(h as int, (h + flen) as int) =~= input@.subrange(e as int, end as int));
            assert(w2.take((h + flen) as int) =~= w2);
            assert(b + w2 =~= s2);
        }
        self.seen = Ghost(s2);
        if !is_buffered(k) {
            self.st = RSt::Frames(o2);
            self.q = Ghost((q + h + flen) as nat);
            self.hn = 0;
            proof {
                assert(unit(srv, lim, w2, st) == Unit::Done(RSt::Frames(o2), (h + flen) as nat, seq![], if kind(t as nat) == Kind::Data { w2.subrange(h as int, (h + flen) as int) } else { seq![] })) by {
                    reveal(unit);
                }
                lemma_advance(srv, lim, b, w2, stt, st, (h + flen) as nat);
                assert(s2.take((q + h + flen) as int) =~= s2);
                assert(s2.skip((q + h + flen) as int) =~= Seq::<u8>::empty());
                assert(self.buf@.take(0) =~= Seq::<u8>::empty());
                lemma_unit_empty(srv, lim, RSt::Frames(o2));
                lemma_run_ext(srv, lim, s2, Seq::<u8>::empty(), stt);
                assert(s2 + Seq::<u8>::empty() =~= s2);
            }
            if matches!(k, Kind::Data) && flen > 0 {
                self.body = Ghost(self.body@ + input@.subrange(e as int, end as int));
                return (Step::Ret(Event::Data(e, end), end), Ghost((steps + 1) as nat));
            }
            proof {
                assert(self.body@ + seq![] =~= self.body@);
            }
            return (Step::Cont(end), Ghost(steps));
        }
        let (res, g) = complete_x(o2, self.server, k, sub(input, e, end));
        match res {
            Err(err) => {
                self.mode = Mode::Failed(err);
                proof {
                    assert(unit(srv, lim, w2, st) == Unit::Fail(err)) by {
                        reveal(unit);
                    }
                    lemma_fail(srv, lim, b, w2, stt, st);
                }
                return (Step::Ret(Event::Error(err), end), Ghost((steps + g@ + 1) as nat));
            },
            Ok((o3, c)) => {
                self.st = RSt::Frames(o3);
                self.q = Ghost((q + h + flen) as nat);
                self.hn = 0;
                let ev = mk_event(c, true, e, end, Ghost(input@), Ghost(self.buf@));
                self.events = Ghost(self.events@.push(ev_view(ev, input@, self.buf@)));
                proof {
                    assert(unit(srv, lim, w2, st) == Unit::Done(RSt::Frames(o3), (h + flen) as nat, seq![cev_view(c, input@.subrange(e as int, end as int))], seq![])) by {
                        reveal(unit);
                    }
                    lemma_advance(srv, lim, b, w2, stt, st, (h + flen) as nat);
                    assert(s2.take((q + h + flen) as int) =~= s2);
                    assert(s2.skip((q + h + flen) as int) =~= Seq::<u8>::empty());
                    assert(self.buf@.take(0) =~= Seq::<u8>::empty());
                    lemma_unit_empty(srv, lim, RSt::Frames(o3));
                    lemma_run_ext(srv, lim, s2, Seq::<u8>::empty(), stt);
                    assert(s2 + Seq::<u8>::empty() =~= s2);
                    assert(o.events@ + seq![cev_view(c, input@.subrange(e as int, end as int))] =~= o.events@.push(cev_view(c, input@.subrange(e as int, end as int))));
                    assert(o.body@ + seq![] =~= o.body@);
                }
                return (Step::Ret(ev, end), Ghost((steps + g@ + 1) as nat));
            },
        }
    }

    /// A frame whose payload goes on past `input`.
    #[verifier::rlimit(80)]
    #[inline(always)]
    fn part(&mut self, input: &[u8], e: usize, t: u64, flen: u64, o2: Order, Ghost(h): Ghost<nat>, Ghost(o): Ghost<Reader>, Ghost(steps): Ghost<nat>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            pre(*old(self), o, input@, e as nat),
            old(self).st is Frames,
            hdr_dec(old(self).seen@.skip(old(self).q@ as int)) == Hdr::Ok(t as nat, flen as nat, h),
            old(self).q@ + h == old(self).seen@.len(),
            accept(old(self).st->Frames_0, old(self).server, old(self).limit as nat, t as nat, flen as nat) == Ok::<Order, u64>(o2),
            steps + 1 <= o.pot() + 4 * e + 32,
            flen > input@.len() - e,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, e as nat),
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost st = self.st;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost stt = start(self.uni@, self.server);
        let k = kind_of(t);
        let len = input.len();
        let avail = len - e;
        proof {
            assert(b + w =~= s);
            lemma_hdr_ok(w);
        }
        let ghost s2 = o.seen@ + input@;
        let ghost w2 = s2.skip(q as int);
        proof {
            assert(input@.take(len as int) =~= input@);
            lemma_cut(o.seen@, input@, e as int, len as int);
            assert(s2.take(q as int) =~= b);
            assert(w2.take(h as int) =~= w);
            assert(w2.take(h as int) =~= w.take(h as int));
            lemma_hdr_same(w, w2, h);
            assert(w2.skip(h as int) =~= input@.skip(e as int));
            assert(b + w2 =~= s2);
            assert(unit(srv, lim, w2, st) is Incomplete) by {
                reveal(unit);
            }
            lemma_stay(srv, lim, b, w2, stt, st);
        }
        self.seen = Ghost(s2);
        self.mode = Mode::Payload;
        self.kind = k;
        self.rem = flen - avail as u64;
        self.st = RSt::Frames(o2);
        self.st0 = Ghost(st);
        self.ty = Ghost(t as nat);
        self.flen = Ghost(flen as nat);
        self.hlen = Ghost(h);
        let ghost st2 = steps;
        if is_buffered(k) {
            self.buf.clear();
            extend(&mut self.buf, sub(input, e, len));
            proof {
                assert(self.buf@ =~= input@.subrange(e as int, len as int));
                assert(input@.subrange(e as int, len as int) =~= input@.skip(e as int));
            }
        }
        if matches!(k, Kind::Data) {
            self.body = Ghost(self.body@ + input@.subrange(e as int, len as int));
            proof {
                assert(input@.subrange(e as int, len as int) =~= input@.skip(e as int));
            }
            if avail > 0 {
                return (Step::Ret(Event::Data(e, len), len), Ghost((steps + avail + 1) as nat));
            }
            proof {
                assert(self.body@ =~= o.body@);
            }
        }
        return (Step::Stop, Ghost((steps + avail) as nat));
    }

    /// A varint unit (stream type or push ID) has been read: `v`, the
    /// last of its bytes `input[..e]`.
    #[inline(always)]
    fn on_var(&mut self, input: &[u8], e: usize, v: u64, Ghost(o): Ghost<Reader>, Ghost(steps): Ghost<nat>, fin: bool) -> (r: (Event, usize, Ghost<nat>))
        requires
            pre(*old(self), o, input@, e as nat),
            !(old(self).st is Frames),
            var_dec(old(self).seen@.skip(old(self).q@ as int)) == Var::Ok(v as nat, (old(self).seen@.len() - old(self).q@) as nat),
            steps + 1 <= o.pot() + 4 * e + 32,
        ensures
            final(self).wf(),
            next_ok(o, *final(self), input@, fin, r.0, r.1 as nat),
            r.2@ + final(self).pot() <= o.pot() + 4 * r.1 + 64,
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost st = self.st;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost n = w.len();
        let ghost stt = start(self.uni@, self.server);
        proof {
            assert(b + w =~= s);
            assert(w.take(n as int) =~= w);
            assert(s.take(s.len() as int) =~= s);
            assert(s.skip(s.len() as int) =~= Seq::<u8>::empty());
            assert(self.buf@.take(0) =~= Seq::<u8>::empty());
            lemma_var_bound(w);
        }
        let ev;
        if matches!(self.st, RSt::Type) {
            match uni_kind_of(v) {
                UniKind::Control => {
                    self.st = RSt::Frames(Order::Control { settings: false, goaway: None, max_push: None });
                    ev = Event::StreamType(v);
                },
                UniKind::Push => {
                    if self.server {
                        self.mode = Mode::Failed(H3_STREAM_CREATION_ERROR);
                        proof {
                            assert(unit(srv, lim, w, st) == Unit::Fail(H3_STREAM_CREATION_ERROR)) by {
                                reveal(unit);
                            }
                            lemma_fail(srv, lim, b, w, stt, st);
                        }
                        return (Event::Error(H3_STREAM_CREATION_ERROR), e, Ghost((steps + 1) as nat));
                    }
                    self.st = RSt::PushId;
                    ev = Event::StreamType(v);
                },
                _ => {
                    self.mode = Mode::Handoff;
                    self.events = Ghost(self.events@.push(Ev::StreamType(v)));
                    proof {
                        assert(unit(srv, lim, w, st) == Unit::Handoff(v, n)) by {
                            reveal(unit);
                        }
                        lemma_handoff(srv, lim, b, w, stt, st, n);
                    }
                    return (Event::StreamType(v), e, Ghost((steps + 1) as nat));
                },
            }
        } else {
            self.st = RSt::Frames(Order::Push(Phase::Start));
            ev = Event::PushId(v);
        }
        self.q = Ghost((q + n) as nat);
        self.hn = 0;
        self.events = Ghost(self.events@.push(ev_view(ev, input@, self.buf@)));
        proof {
            assert(unit(srv, lim, w, st) == Unit::Done(self.st, n, seq![ev_view(ev, input@, self.buf@)], seq![])) by {
                reveal(unit);
            }
            lemma_advance(srv, lim, b, w, stt, st, n);
            lemma_unit_empty(srv, lim, self.st);
            lemma_run_ext(srv, lim, s, Seq::<u8>::empty(), stt);
            assert(s + Seq::<u8>::empty() =~= s);
            assert(o.body@ + seq![] =~= o.body@);
            assert(o.events@ + seq![ev_view(ev, input@, self.buf@)] =~= o.events@.push(ev_view(ev, input@, self.buf@)));
        }
        (ev, e, Ghost((steps + 1) as nat))
    }

    /// The input ran out with the stream's next unit incomplete.
    #[inline(always)]
    fn short(&mut self, input: &[u8], pos: usize, fin: bool, Ghost(o): Ghost<Reader>, Ghost(steps): Ghost<nat>) -> (r: (Event, usize, Ghost<nat>))
        requires
            old(self).wf(),
            old(self).mode is Unit,
            old(self).hn == 0,
            same_cfg(o, *old(self)),
            old(self).uni@ == o.uni@,
            old(self).seen@ == o.seen@ + input@.take(pos as int),
            old(self).events@ == o.events@,
            old(self).body@ == o.body@,
            pos < input@.len(),
            old(self).st is Frames ==> hdr_dec(input@.skip(pos as int)) is Short,
            !(old(self).st is Frames) ==> var_dec(input@.skip(pos as int)) is Short,
            steps <= o.pot() + 4 * pos + 32,
        ensures
            final(self).wf(),
            next_ok(o, *final(self), input@, fin, r.0, r.1 as nat),
            r.2@ + final(self).pot() <= o.pot() + 4 * r.1 + 64,
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost stt = start(self.uni@, self.server);
        let len = input.len();
        self.buf.clear();
        extend(&mut self.buf, sub(input, pos, len));
        self.hn = len - pos;
        let ghost s2 = o.seen@ + input@;
        proof {
            assert(s.skip(q as int).len() == 0);
            assert(s.take(q as int) =~= s);
            assert(input@.take(len as int) =~= input@);
            lemma_cut(o.seen@, input@, pos as int, len as int);
            assert(s2.take(q as int) =~= s);
            assert(s2.skip(q as int) =~= input@.skip(pos as int));
            assert(self.buf@.take(self.hn as int) =~= input@.skip(pos as int));
            assert(unit(srv, lim, input@.skip(pos as int), self.st) is Incomplete) by {
                reveal(unit);
            }
            lemma_stay(srv, lim, s, input@.skip(pos as int), stt, self.st);
            assert(s + input@.skip(pos as int) =~= s2);
        }
        self.seen = Ghost(s2);
        self.finish(input, fin, Ghost(o), Ghost((steps + (len - pos)) as nat))
    }

    /// All the input has been used.
    #[inline(always)]
    fn finish(&mut self, input: &[u8], fin: bool, Ghost(o): Ghost<Reader>, Ghost(steps): Ghost<nat>) -> (r: (Event, usize, Ghost<nat>))
        requires
            old(self).wf(),
            old(self).mode is Unit || old(self).mode is Payload,
            same_cfg(o, *old(self)),
            old(self).seen@ == o.seen@ + input@,
            old(self).events@ == o.events@,
            old(self).body@ == o.body@,
            steps + old(self).pot() + 1 <= o.pot() + 4 * input@.len() + 64,
        ensures
            final(self).wf(),
            next_ok(o, *final(self), input@, fin, r.0, r.1 as nat),
            r.2@ + final(self).pot() <= o.pot() + 4 * r.1 + 64,
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let len = input.len();
        proof {
            assert(input@.take(len as int) =~= input@);
        }
        if !fin {
            return (Event::Need, len, Ghost((steps + 1) as nat));
        }
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost stt = start(self.uni@, self.server);
        proof {
            assert(b + w =~= s);
            if self.mode is Unit {
                assert(unit(srv, lim, w, self.st) is Incomplete) by {
                    reveal(unit);
                }
                lemma_stay(srv, lim, b, w, stt, self.st);
            } else {
                lemma_hdr_ok(w);
                assert(unit(srv, lim, w, self.st0@) is Incomplete) by {
                    reveal(unit);
                }
                lemma_stay(srv, lim, b, w, stt, self.st0@);
            }
            reveal(end_of);
        }
        let res: Result<(), u64> = if matches!(self.mode, Mode::Payload) {
            Err(H3_FRAME_ERROR)
        } else {
            match self.st {
                RSt::Type => Ok(()),
                RSt::PushId => Err(H3_MESSAGE_ERROR),
                RSt::Frames(od) => {
                    if self.hn > 0 {
                        Err(H3_FRAME_ERROR)
                    } else {
                        match od {
                            Order::Control { .. } => Err(H3_CLOSED_CRITICAL_STREAM),
                            Order::Request(Phase::Start) => Err(H3_REQUEST_INCOMPLETE),
                            Order::Response(Phase::Start) | Order::Push(Phase::Start) => Err(H3_MESSAGE_ERROR),
                            _ => Ok(()),
                        }
                    }
                },
            }
        };
        match res {
            Ok(()) => {
                self.mode = Mode::Ended;
                (Event::End, len, Ghost((steps + 1) as nat))
            },
            Err(e) => {
                self.mode = Mode::Failed(e);
                (Event::Error(e), len, Ghost((steps + 1) as nat))
            },
        }
    }

    /// Picks up inside a frame's payload.
    fn resume(&mut self, input: &[u8], Ghost(o): Ghost<Reader>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            *old(self) == o,
            o.wf(),
            o.mode is Payload,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, 0),
    {
        if (input.len() as u64) < self.rem {
            self.resume_part(input, Ghost(o), fin)
        } else {
            self.resume_done(input, Ghost(o), fin)
        }
    }

    /// The payload goes on past `input`.
    #[verifier::rlimit(80)]
    fn resume_part(&mut self, input: &[u8], Ghost(o): Ghost<Reader>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            *old(self) == o,
            o.wf(),
            o.mode is Payload,
            (input@.len() as u64) < o.rem,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, 0),
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost h = self.hlen@;
        let ghost flen = self.flen@;
        let ghost st0 = self.st0@;
        let ghost stt = start(self.uni@, self.server);
        let avail = input.len();
        let rem = self.rem;
        let k = self.kind;
        proof {
            assert(b + w =~= s);
            lemma_hdr_ok(w);
        }
        self.rem = rem - avail as u64;
        if is_buffered(k) {
            extend(&mut self.buf, input);
        }
        let ghost s2 = s + input@;
        let ghost w2 = s2.skip(q as int);
        proof {
            assert(input@.take(avail as int) =~= input@);
            assert(s2.take(q as int) =~= b);
            assert(w2 =~= w + input@);
            assert(w2.take(h as int) =~= w.take(h as int));
            lemma_hdr_same(w, w2, h);
            assert(w2.skip(h as int) =~= w.skip(h as int) + input@);
            assert(b + w2 =~= s2);
            assert(unit(srv, lim, w2, st0) is Incomplete) by {
                reveal(unit);
            }
            assert(unit(srv, lim, w, st0) is Incomplete) by {
                reveal(unit);
            }
            lemma_stay(srv, lim, b, w2, stt, st0);
            lemma_stay(srv, lim, b, w, stt, st0);
        }
        self.seen = Ghost(s2);
        if matches!(k, Kind::Data) {
            self.body = Ghost(self.body@ + input@);
            proof {
                assert(o.body@ + input@ =~= o.body@ + input@.subrange(0, avail as int));
                let rb = run(srv, lim, b, stt).body;
                assert((rb + w.skip(h as int)) + input@ =~= rb + (w.skip(h as int) + input@));
            }
            if avail > 0 {
                return (Step::Ret(Event::Data(0, avail), avail), Ghost((avail + 1) as nat));
            }
        }
        return (Step::Stop, Ghost((avail + 1) as nat));
    }

    /// The payload ends in `input`.
    #[verifier::rlimit(80)]
    fn resume_done(&mut self, input: &[u8], Ghost(o): Ghost<Reader>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            *old(self) == o,
            o.wf(),
            o.mode is Payload,
            (input@.len() as u64) >= o.rem,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, 0),
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost srv = self.server;
        let ghost lim = self.limit as nat;
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost b = s.take(q as int);
        let ghost w = s.skip(q as int);
        let ghost h = self.hlen@;
        let ghost flen = self.flen@;
        let ghost st0 = self.st0@;
        let ghost stt = start(self.uni@, self.server);
        let avail = input.len();
        let rem = self.rem;
        let k = self.kind;
        proof {
            assert(b + w =~= s);
            lemma_hdr_ok(w);
        }
        let end = rem as usize;
        let ghost s2 = s + input@.take(end as int);
        let ghost w2 = s2.skip(q as int);
        proof {
            assert(s2.take(q as int) =~= b);
            assert(w2 =~= w + input@.take(end as int));
            assert(w2.take(h as int) =~= w.take(h as int));
            lemma_hdr_same(w, w2, h);
            assert(w2.len() == h + flen);
            assert(w2.take((h + flen) as int) =~= w2);
            assert(w2.subrange(h as int, (h + flen) as int) =~= w.skip(h as int) + input@.take(end as int));
            assert(b + w2 =~= s2);
            assert(s2.take((q + h + flen) as int) =~= s2);
            assert(s2.skip((q + h + flen) as int) =~= Seq::<u8>::empty());
            lemma_unit_empty(srv, lim, self.st);
            assert(unit(srv, lim, w, st0) is Incomplete) by {
                reveal(unit);
            }
            lemma_stay(srv, lim, b, w, stt, st0);
        }
        self.seen = Ghost(s2);
        if !is_buffered(k) {
            self.mode = Mode::Unit;
            self.hn = 0;
            self.q = Ghost((q + h + flen) as nat);
            proof {
                assert(unit(srv, lim, w2, st0) == Unit::Done(self.st, (h + flen) as nat, seq![], if kind(self.ty@) == Kind::Data { w2.subrange(h as int, (h + flen) as int) } else { seq![] })) by {
                    reveal(unit);
                }
                lemma_advance(srv, lim, b, w2, stt, st0, (h + flen) as nat);
                assert(self.buf@.take(0) =~= Seq::<u8>::empty());
                lemma_run_ext(srv, lim, s2, Seq::<u8>::empty(), stt);
                assert(s2 + Seq::<u8>::empty() =~= s2);
            }
            if matches!(k, Kind::Data) {
                self.body = Ghost(self.body@ + input@.subrange(0, end as int));
                proof {
                    assert(input@.subrange(0, end as int) =~= input@.take(end as int));
                    let rb = run(srv, lim, b, stt).body;
                    assert((rb + w.skip(h as int)) + input@.take(end as int) =~= rb + (w.skip(h as int) + input@.take(end as int)));
                }
                return (Step::Ret(Event::Data(0, end), end), Ghost(1));
            }
            proof {
                assert(o.body@ + seq![] =~= o.body@);
            }
            return (Step::Cont(end), Ghost(0));
        }
        extend(&mut self.buf, sub(input, 0, end));
        proof {
            assert(input@.subrange(0, end as int) =~= input@.take(end as int));
        }
        let o2 = match self.st {
            RSt::Frames(x) => x,
            _ => Order::Request(Phase::Start),
        };
        proof {
            assert(self.buf@ =~= w2.subrange(h as int, (h + flen) as int));
        }
        let (res, g) = complete_x(o2, self.server, k, self.buf.as_slice());
        match res {
            Err(err) => {
                self.mode = Mode::Failed(err);
                proof {
                    assert(unit(srv, lim, w2, st0) == Unit::Fail(err)) by {
                        reveal(unit);
                    }
                    lemma_fail(srv, lim, b, w2, stt, st0);
                }
                assert(self.wf());
                assert(next_ok(o, *self, input@, fin, Event::Error(err), end as nat));
                assert(end + g@ + 1 + self.pot() <= o.pot() + 4 * end + 64);
                (Step::Ret(Event::Error(err), end), Ghost((end + g@ + 1) as nat))
            },
            Ok((o3, c)) => {
                self.st = RSt::Frames(o3);
                self.mode = Mode::Unit;
                self.q = Ghost((q + h + flen) as nat);
                self.hn = 0;
                let ghost blen = self.buf@.len();
                let ev = mk_event(c, false, 0, self.buf.len(), Ghost(input@), Ghost(self.buf@));
                self.events = Ghost(self.events@.push(ev_view(ev, input@, self.buf@)));
                proof {
                    assert(unit(srv, lim, w2, st0) == Unit::Done(RSt::Frames(o3), (h + flen) as nat, seq![cev_view(c, self.buf@)], seq![])) by {
                        reveal(unit);
                    }
                    lemma_advance(srv, lim, b, w2, stt, st0, (h + flen) as nat);
                    assert(self.buf@.take(0) =~= Seq::<u8>::empty());
                    lemma_unit_empty(srv, lim, RSt::Frames(o3));
                    lemma_run_ext(srv, lim, s2, Seq::<u8>::empty(), stt);
                    assert(s2 + Seq::<u8>::empty() =~= s2);
                    assert(o.events@ + seq![ev_view(ev, input@, self.buf@)] =~= o.events@.push(ev_view(ev, input@, self.buf@)));
                    assert(o.body@ + seq![] =~= o.body@);
                }
                assert(self.wf());
                assert(next_ok(o, *self, input@, fin, ev, end as nat));
                assert(end + g@ + 1 + self.pot() <= o.pot() + 4 * end + 64);
                (Step::Ret(ev, end), Ghost((end + g@ + 1) as nat))
            },
        }
    }

    /// Picks up with the first `hn` bytes of a unit in `buf`.
    #[verifier::rlimit(200)]
    fn window(&mut self, input: &[u8], Ghost(o): Ghost<Reader>, fin: bool) -> (r: (Step, Ghost<nat>))
        requires
            *old(self) == o,
            o.wf(),
            o.mode is Unit,
            o.hn > 0,
        ensures
            step_ok(o, *final(self), input@, fin, r.0, r.1@, 0),
    {
        hide(run);
        hide(unit);
        hide(end_of);
        let ghost q = self.q@;
        let ghost s = self.seen@;
        let ghost w = s.skip(q as int);
        let hn = self.hn;
        proof {
            lemma_short_len(w);
        }
        self.buf.truncate(hn);
        let cap = 16 - hn;
        let k = if input.len() < cap {
            input.len()
        } else {
            cap
        };
        extend(&mut self.buf, sub(input, 0, k));
        let ghost win = w + input@.take(k as int);
        proof {
            assert(self.buf@ =~= win);
            assert(self.buf@.skip(0) =~= win);
            assert(input@.subrange(0, k as int) =~= input@.take(k as int));
        }
        match self.st {
            RSt::Frames(_) => {
                match read_hdr(self.buf.as_slice(), 0) {
                    None => {
                        proof {
                            lemma_short_len(win);
                            assert(k == input.len());
                            assert(input@.take(k as int) =~= input@);
                            assert((s + input@).take(q as int) =~= s.take(q as int));
                            assert((s + input@).skip(q as int) =~= win);
                            assert(self.buf@.take((hn + k) as int) =~= win);
                            assert(unit(self.server, self.limit as nat, win, self.st) is Incomplete) by {
                                reveal(unit);
                            }
                            assert(unit(self.server, self.limit as nat, w, self.st) is Incomplete) by {
                                reveal(unit);
                            }
                            lemma_stay(self.server, self.limit as nat, s.take(q as int), win, start(self.uni@, self.server), self.st);
                            assert(s.take(q as int) + win =~= s + input@);
                            assert(s.take(q as int) + w =~= s);
                            lemma_stay(self.server, self.limit as nat, s.take(q as int), w, start(self.uni@, self.server), self.st);
                        }
                        self.hn = hn + k;
                        self.seen = Ghost(s + input@);
                        (Step::Stop, Ghost((k + 1) as nat))
                    },
                    Some((t, flen, he)) => {
                        proof {
                            if he <= hn {
                                assert(w.take(he as int) =~= win.take(he as int));
                                lemma_hdr_same(win, w, he as nat);
                            }
                        }
                        let e = he - hn;
                        let ghost s2 = s + input@.take(e as int);
                        proof {
                            assert(s2.take(q as int) =~= s.take(q as int));
                            assert(s2.skip(q as int) =~= win.take(he as int));
                            assert(win.take(he as int).take(he as int) =~= win.take(he as int));
                            lemma_hdr_same(win, win.take(he as int), he as nat);
                        }
                        self.seen = Ghost(s2);
                        self.on_hdr(input, e, t, flen, Ghost(he as nat), Ghost(o), Ghost((k + 1) as nat), fin)
                    },
                }
            },
            _ => {
                match read_var(self.buf.as_slice(), 0) {
                    None => {
                        proof {
                            lemma_short_len(win);
                            assert(k == input.len());
                            assert(input@.take(k as int) =~= input@);
                            assert((s + input@).take(q as int) =~= s.take(q as int));
                            assert((s + input@).skip(q as int) =~= win);
                            assert(self.buf@.take((hn + k) as int) =~= win);
                            assert(unit(self.server, self.limit as nat, win, self.st) is Incomplete) by {
                                reveal(unit);
                            }
                            assert(unit(self.server, self.limit as nat, w, self.st) is Incomplete) by {
                                reveal(unit);
                            }
                            lemma_stay(self.server, self.limit as nat, s.take(q as int), win, start(self.uni@, self.server), self.st);
                            assert(s.take(q as int) + win =~= s + input@);
                            assert(s.take(q as int) + w =~= s);
                            lemma_stay(self.server, self.limit as nat, s.take(q as int), w, start(self.uni@, self.server), self.st);
                        }
                        self.hn = hn + k;
                        self.seen = Ghost(s + input@);
                        (Step::Stop, Ghost((k + 1) as nat))
                    },
                    Some((v, he)) => {
                        proof {
                            if he <= hn {
                                assert(w.take(he as int) =~= win.take(he as int));
                                lemma_var_same(win, w, he as nat);
                            }
                        }
                        let e = he - hn;
                        let ghost s2 = s + input@.take(e as int);
                        proof {
                            assert(s2.take(q as int) =~= s.take(q as int));
                            assert(s2.skip(q as int) =~= win.take(he as int));
                            assert(win.take(he as int).take(he as int) =~= win.take(he as int));
                            lemma_var_same(win, win.take(he as int), he as nat);
                        }
                        self.seen = Ghost(s2);
                        let (ev, u, g) = self.on_var(input, e, v, Ghost(o), Ghost((k + 1) as nat), fin);
                        (Step::Ret(ev, u), g)
                    },
                }
            },
        }
    }
}

/// The reader's configuration did not change.
pub open spec fn same_cfg(o: Reader, n: Reader) -> bool {
    &&& n.is_server() == o.is_server()
    &&& n.lim() == o.lim()
    &&& n.st_start() == o.st_start()
}

/// What `next(input, fin)` guarantees, from reader `o` to reader `n`,
/// returning event `e` having used `used` bytes.
pub open spec fn next_ok(o: Reader, n: Reader, input: Seq<u8>, fin: bool, e: Event, used: nat) -> bool {
    let srv = o.is_server();
    let lim = o.lim();
    let st = o.st_start();
    &&& used <= input.len()
    &&& same_cfg(o, n)
    &&& n.seen() == o.seen() + input.take(used as int)
    // The events and DATA so far are the spec's, for the stream so far.
    &&& n.events() == run(srv, lim, n.seen(), st).ev
    &&& match e {
        Event::Need => used == input.len() && !fin && n.events() == o.events() && n.body() == o.body(),
        Event::Data(a, b) => a < b <= used && n.events() == o.events() && n.body() == o.body() + input.subrange(a as int, b as int),
        // The stream ended well formed. (`fin` was given, now or before.)
        Event::End => end_of(srv, lim, n.seen(), st) == Ok::<(), u64>(()) && n.events() == o.events(),
        // The stream is in error: as far as it has been read, or because
        // it ended (`fin`) where it may not.
        Event::Error(c) => run(srv, lim, n.seen(), st).tail == Tail::Fail(c) || (run(srv, lim, n.seen(), st).tail is At && end_of(srv, lim, n.seen(), st) == Err::<(), u64>(c)),
        Event::Handoff => used == 0 && run(srv, lim, n.seen(), st).tail is Handoff && n.events() == o.events(),
        _ => n.events() == o.events().push(ev_view(e, input, n.buf_v())) && n.body() == o.body() && ev_ok(e, input, n.buf_v(), used),
    }
}

} // verus!
