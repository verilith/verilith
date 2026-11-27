//! The HTTP/3 connection core (RFC 9114), verified: what `h3.rs` does
//! with the bytes of each stream, between QUIC and the handler.
//!
//! - [`Req3`]: a request stream's lifecycle. It wraps verilith-h3's
//!   verified [`Reader`]; the request it hands out ([`Act::Ready`], at most
//!   once per stream) is one whose stream ended well formed under the
//!   reader's specification, whose body is exactly the stream's DATA
//!   content (or is over the limit, and answered 413), and whose
//!   Content-Length, if any, is that content's length (§4.1.2).
//! - [`frame_head`]: a response's framing. `head + body` is the HEADERS
//!   frame with the encoded section, then one DATA frame with the body
//!   (none when the body is empty), and the client's reader reads it
//!   back as exactly that: one HEADERS event, the body as content, a
//!   well-formed end ([`lemma_response_rt`]).
//! - [`control_preamble`]: our control stream begins with its type and
//!   our SETTINGS, and nothing else (§6.2.1).
//! - [`Uni3`]: a unidirectional stream the peer opened. At most one
//!   control stream and one of each QPACK stream (§6.2.1, RFC 9204
//!   §4.2), none of them closed, unknown types discarded (§6.2.3), and the
//!   bytes handed to QPACK exactly the stream's bytes after its type.
//! - [`Budget`]: the flood defence. Requests the peer abandons (reset
//!   before their end, or refused) cost a unit each; a complete request
//!   earns `per_request`; the connection is closed with
//!   H3_EXCESSIVE_LOAD once the cost passes what was earned.
use vstd::prelude::*;
use verilith_h3::consts::*;
use verilith_h3::reader::{Reader, Event, Src};
#[cfg(verus_keep_ghost)]
use verilith_h3::reader::{next_ok, ev_view, src_view};
use verilith_h3::spec::{UniKind, UniSeen, Settings};
#[cfg(verus_keep_ghost)]
use verilith_h3::spec::*;
#[cfg(verus_keep_ghost)]
use verilith_h3::encode::{wrote, lemma_unit_rt, frame_ev, frame_data};
use verilith_core::prims::extend;
use verilith_core::clen::BodyLen;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------
// Our control stream.

/// The SETTINGS we send: no dynamic table (capacity 0 and no blocked
/// streams are the defaults, so they are left out), and the largest field
/// section we take.
pub open spec fn our_settings(max_field_section: u64) -> Settings {
    Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: Some(max_field_section),
        qpack_blocked_streams: None,
        enable_connect_protocol: None,
        h3_datagram: None,
    }
}

/// The bytes our control stream starts with: its type, then SETTINGS.
pub open spec fn preamble(max_field_section: u64) -> Seq<u8> {
    var_enc(STREAM_CONTROL as nat) + frame_enc(Frame::Settings(our_settings(max_field_section)))
}

/// Writes the start of our control stream into `out`; returns its length,
/// or 0 if `max_field_section` is not a varint (over 2^62 - 1).
pub fn control_preamble(max_field_section: u64, out: &mut [u8; 64]) -> (r: usize)
    ensures
        r > 0 ==> r <= 64 && final(out)@.subrange(0, r as int) == preamble(max_field_section)
            && settings_ok(our_settings(max_field_section)),
{
    if max_field_section > MAX_VARINT {
        return 0;
    }
    let s = Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: Some(max_field_section),
        qpack_blocked_streams: None,
        enable_connect_protocol: None,
        h3_datagram: None,
    };
    let ghost o = out@;
    let at = match verilith_h3::write_var(out, 0, STREAM_CONTROL) {
        Some(a) => a,
        None => return 0,
    };
    let ghost m = out@;
    let end = match verilith_h3::write_settings(out, at, &s) {
        Some(e) => e,
        None => return 0,
    };
    proof {
        verilith_h3::encode::lemma_wrote_seq(o, m, out@, 0, at as int, end as int,
            var_enc(STREAM_CONTROL as nat), frame_enc(Frame::Settings(s)));
    }
    end
}

// ---------------------------------------------------------------------
// A response's framing.

/// A response on the wire: HEADERS with the encoded field section, then,
/// if there is a body, one DATA frame with it.
pub open spec fn response(section: Seq<u8>, body: Seq<u8>) -> Seq<u8> {
    frame_enc(Frame::Headers(section)) + if body.len() == 0 {
        Seq::<u8>::empty()
    } else {
        frame_enc(Frame::Data(body))
    }
}

/// The part of [`response`] before the body: the HEADERS frame and the
/// DATA frame's header.
pub open spec fn response_head(section: Seq<u8>, body_len: nat) -> Seq<u8> {
    frame_enc(Frame::Headers(section)) + if body_len == 0 {
        Seq::<u8>::empty()
    } else {
        var_enc(DATA as nat) + var_enc(body_len)
    }
}

pub proof fn lemma_head_body(section: Seq<u8>, body: Seq<u8>)
    ensures
        response_head(section, body.len()) + body == response(section, body),
{
    if body.len() == 0 {
        assert(response_head(section, 0) + body =~= response(section, body));
    } else {
        assert(response_head(section, body.len()) + body =~= response(section, body));
    }
}

/// One HEADERS or DATA frame at the start of `s`, on a response stream
/// in phase `p` at the client: exactly that frame, and the phase after it.
proof fn lemma_unit_frame(lim: nat, p: Phase, f: Frame, rest: Seq<u8>, p2: Phase)
    requires
        frame_ok(f),
        f is Headers || f is Data,
        f is Headers ==> p == Phase::Start && p2 == Phase::Head && payload_enc(f).len() <= lim,
        f is Data ==> (p == Phase::Head || p == Phase::Body) && p2 == Phase::Body,
    ensures
        unit(false, lim, frame_enc(f) + rest, RSt::Frames(Order::Response(p)))
            == Unit::Done(RSt::Frames(Order::Response(p2)), frame_enc(f).len(), frame_ev(f), frame_data(f)),
{
    let o = Order::Response(p);
    let t = frame_type(f);
    let pl = payload_enc(f);
    let s = frame_enc(f) + rest;
    verilith_h3::varint::lemma_var_enc(t);
    verilith_h3::varint::lemma_var_enc(pl.len());
    assert(s =~= var_enc(t) + var_enc(pl.len()) + (pl + rest));
    verilith_h3::encode::lemma_hdr_rt(t, pl.len(), pl + rest);
    let h = var_size(t) + var_size(pl.len());
    assert(s.subrange(h as int, (h + pl.len()) as int) =~= pl);
    assert(kind(t) == if f is Headers { Kind::Headers } else { Kind::Data });
    assert(accept(o, false, lim, t, pl.len()) == Ok::<Order, u64>(Order::Response(p2)));
}

/// The client's reader on a stream that is empty from here on.
proof fn lemma_run_empty(lim: nat, st: RSt)
    requires
        st is Frames,
    ensures
        run(false, lim, Seq::<u8>::empty(), st) == (Out { ev: seq![], body: seq![], tail: Tail::At(st, 0) }),
{
    verilith_h3::lemmas::lemma_unit_empty(false, lim, st);
}

/// The response round trip: the client's reader (verilith-h3's
/// specification, RFC 9114 §4.1 and §7) reads [`response`] as exactly one
/// HEADERS frame with `section`, then `body` as the content, ending well
/// formed.
pub proof fn lemma_response_rt(lim: nat, section: Seq<u8>, body: Seq<u8>)
    requires
        section.len() <= lim,
        section.len() <= MAX_VARINT,
        body.len() <= MAX_VARINT,
    ensures
        run(false, lim, response(section, body), start(false, false)).ev == seq![Ev::Headers(section)],
        run(false, lim, response(section, body), start(false, false)).body == body,
        end_of(false, lim, response(section, body), start(false, false)) == Ok::<(), u64>(()),
{
    let fh = Frame::Headers(section);
    let eh = frame_enc(fh);
    let s = response(section, body);
    let st0 = RSt::Frames(Order::Response(Phase::Start));
    let st1 = RSt::Frames(Order::Response(Phase::Head));
    let st2 = RSt::Frames(Order::Response(Phase::Body));
    let tail = if body.len() == 0 { Seq::<u8>::empty() } else { frame_enc(Frame::Data(body)) };
    assert(s == eh + tail);
    lemma_unit_frame(lim, Phase::Start, fh, tail, Phase::Head);
    assert(eh.len() > 0);
    assert(s.skip(eh.len() as int) =~= tail);
    if body.len() == 0 {
        lemma_run_empty(lim, st1);
        let r1 = run(false, lim, tail, st1);
        assert(run(false, lim, s, st0) == (Out { ev: seq![Ev::Headers(section)] + r1.ev, body: seq![] + r1.body, tail: shift(r1.tail, eh.len()) }));
        assert(seq![Ev::Headers(section)] + r1.ev =~= seq![Ev::Headers(section)]);
        assert(Seq::<u8>::empty() + r1.body =~= body);
        assert(s.skip(eh.len() as int) =~= Seq::<u8>::empty());
    } else {
        let fd = Frame::Data(body);
        let ed = frame_enc(fd);
        lemma_unit_frame(lim, Phase::Head, fd, Seq::<u8>::empty(), Phase::Body);
        assert(ed + Seq::<u8>::empty() =~= ed);
        assert(ed.len() > 0);
        assert(ed.skip(ed.len() as int) =~= Seq::<u8>::empty());
        lemma_run_empty(lim, st2);
        let r2 = run(false, lim, Seq::<u8>::empty(), st2);
        assert(run(false, lim, ed, st1) == (Out { ev: seq![] + r2.ev, body: body + r2.body, tail: shift(r2.tail, ed.len()) }));
        let r1 = run(false, lim, ed, st1);
        assert(r1.ev =~= Seq::<Ev>::empty());
        assert(r1.body =~= body);
        assert(run(false, lim, s, st0) == (Out { ev: seq![Ev::Headers(section)] + r1.ev, body: seq![] + r1.body, tail: shift(r1.tail, eh.len()) }));
        assert(seq![Ev::Headers(section)] + r1.ev =~= seq![Ev::Headers(section)]);
        assert(Seq::<u8>::empty() + r1.body =~= body);
        assert(s.skip((eh.len() + ed.len()) as int) =~= Seq::<u8>::empty());
    }
}

/// Appends the head of a response with `section` and a body of
/// `body_len` bytes to `head`; false (appending nothing) if either length
/// is over 2^62 - 1.
pub fn frame_head(head: &mut Vec<u8>, section: &[u8], body_len: usize) -> (r: bool)
    ensures
        r ==> final(head)@ == old(head)@ + response_head(section@, body_len as nat),
        !r ==> final(head)@ == old(head)@,
        r == (section@.len() <= MAX_VARINT && body_len <= MAX_VARINT),
{
    if section.len() as u64 > MAX_VARINT || body_len as u64 > MAX_VARINT {
        return false;
    }
    let mut b = [0u8; 16];
    let _ = verilith_h3::encode::header_size(HEADERS, section.len() as u64);
    let n = verilith_h3::encode::put_header(&mut b, 0, HEADERS, section.len() as u64);
    let ghost h0 = head@;
    extend(head, slice_subrange(&b, 0, n));
    extend(head, section);
    let ghost h1 = head@;
    proof {
        assert(b@.subrange(0, n as int) == var_enc(HEADERS as nat) + var_enc(section@.len()));
        assert(h1 =~= h0 + frame_enc(Frame::Headers(section@)));
    }
    if body_len > 0 {
        let mut d = [0u8; 16];
        let _ = verilith_h3::encode::header_size(DATA, body_len as u64);
        let m = verilith_h3::encode::put_header(&mut d, 0, DATA, body_len as u64);
        extend(head, slice_subrange(&d, 0, m));
        proof {
            assert(head@ =~= h0 + response_head(section@, body_len as nat));
        }
    } else {
        proof {
            assert(head@ =~= h0 + response_head(section@, body_len as nat));
        }
    }
    true
}

// ---------------------------------------------------------------------
// A request stream.

/// What [`Req3::step`] asks of its caller.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Act {
    /// All of the input was used; more is needed.
    Need,
    /// The request's field section, to QPACK-decode: `input[a..b]`
    /// (`Src::Input`, positions in the whole input) or the reader's buffer
    /// from `off` (`Src::Buf`). Then call `step` again with the rest.
    Headers(Src),
    /// A trailer section (a second HEADERS frame), as `Headers`: to
    /// QPACK-decode, for its errors only (trailers are not passed on).
    Trailers(Src),
    /// The request is complete: answer it. Returned once per stream.
    Ready,
    /// The request is malformed (§4.1.2): reset the stream with
    /// H3_MESSAGE_ERROR.
    Malformed,
    /// A connection error, with this code.
    Close(u64),
    /// The stream was ready before; nothing more to do.
    Done,
}

/// A request stream, at the server.
pub struct Req3 {
    r: Reader,
    /// The body, while it is within `max_body`.
    body: Vec<u8>,
    too_big: bool,
    got_headers: bool,
    /// DATA payload bytes received, against the Content-Length declared
    /// (verilith-core's shared check, as HTTP/2's).
    len: BodyLen,
    ended: bool,
    /// The stream failed (a connection error or a malformed request was
    /// reported): it is not read again.
    dead: bool,
    max_body: usize,
    /// The first HEADERS frame's section.
    head: Ghost<Seq<u8>>,
    /// The DATA payload the reader reported, in order.
    data: Ghost<Seq<u8>>,
}

impl Req3 {
    pub closed spec fn seen(&self) -> Seq<u8> {
        self.r.seen()
    }

    /// The request's encoded field section.
    pub closed spec fn section(&self) -> Seq<u8> {
        self.head@
    }

    /// The stream's content: the DATA payload the verified reader reported.
    pub closed spec fn content(&self) -> Seq<u8> {
        self.data@
    }

    pub closed spec fn limit(&self) -> nat {
        self.r.lim()
    }

    pub closed spec fn max_body_s(&self) -> nat {
        self.max_body as nat
    }

    pub closed spec fn is_ended(&self) -> bool {
        self.ended
    }

    pub closed spec fn body_v(&self) -> Seq<u8> {
        self.body@
    }

    pub closed spec fn too_big_s(&self) -> bool {
        self.too_big
    }

    pub closed spec fn cl_s(&self) -> Option<u64> {
        self.len.declared()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.r.wf()
        &&& self.r.is_server()
        &&& self.r.st_start() == start(false, true)
        &&& self.body@.len() <= self.max_body
        &&& !self.dead ==> {
            &&& (!self.too_big ==> self.body@ == self.data@)
            &&& (self.too_big ==> self.data@.len() > self.max_body)
            &&& (self.got_headers ==> self.r.events().len() > 0 && self.r.events()[0] == Ev::Headers(self.head@))
            &&& self.len.got() == self.data@.len()
            &&& (!self.got_headers ==> self.r.events().len() == 0)
            &&& self.len.inv()
        }
        &&& self.ended ==> {
            &&& end_of(true, self.r.lim(), self.r.seen(), start(false, true)) == Ok::<(), u64>(())
            &&& self.got_headers
            &&& !self.dead
        }
    }

    /// What a request handed out by `step` ([`Act::Ready`]) is: its
    /// stream, as far as it was read, ended well formed under verilith-h3's
    /// specification (§4.1: HEADERS, DATA, optional trailers; §7: every
    /// frame well formed); it began with the HEADERS frame carrying
    /// `section()`; its body is the stream's content, unless that was over
    /// `max_body` (and the request is answered 413); and a Content-Length
    /// it declared is the content's length (§4.1.2).
    pub open spec fn ready(&self) -> bool {
        &&& self.wf()
        &&& self.is_ended()
        &&& end_of(true, self.limit(), self.seen(), start(false, true)) == Ok::<(), u64>(())
        &&& (!self.too_big_s() ==> self.body_v() == self.content())
        &&& (self.too_big_s() ==> self.content().len() > self.max_body_s())
        &&& (self.cl_s() matches Some(n) ==> n as nat == self.content().len())
    }

    pub fn new(max_field_section: u64, max_body: usize) -> (r: Req3)
        ensures
            r.wf(),
            r.seen() == Seq::<u8>::empty(),
            !r.is_ended(),
    {
        Req3 {
            r: Reader::new_request(true, max_field_section),
            body: Vec::new(),
            too_big: false,
            got_headers: false,
            len: BodyLen::new(),
            ended: false,
            dead: false,
            max_body,
            head: Ghost(Seq::empty()),
            data: Ghost(Seq::empty()),
        }
    }

    /// A fresh stream, keeping the body's buffer.
    pub fn reset(&mut self, max_field_section: u64, max_body: usize)
        ensures
            final(self).wf(),
            final(self).seen() == Seq::<u8>::empty(),
            !final(self).is_ended(),
    {
        self.r = Reader::new_request(true, max_field_section);
        self.body.clear();
        self.too_big = false;
        self.got_headers = false;
        self.len = BodyLen::new();
        self.ended = false;
        self.dead = false;
        self.max_body = max_body;
        self.head = Ghost(Seq::empty());
        self.data = Ghost(Seq::empty());
        proof {
            assert(self.body@ =~= Seq::<u8>::empty());
        }
    }

    /// The body, for the handler.
    pub fn body(&self) -> (r: &[u8])
        ensures
            r@ == self.body_v(),
    {
        self.body.as_slice()
    }

    /// The body went over `max_body`.
    pub fn too_big(&self) -> (r: bool)
        ensures
            r == self.too_big_s(),
    {
        self.too_big
    }

    pub closed spec fn buf_v(&self) -> Seq<u8> {
        self.r.buf_v()
    }

    /// The reader's buffer, for `Src::Buf` sections.
    pub fn buffered(&self) -> (r: &[u8])
        ensures
            r@ == self.buf_v(),
    {
        self.r.buffered()
    }

    /// A Content-Length field line's value `v`, from the decoded section:
    /// false if it is not a decimal length, differs from one declared
    /// before, or is less than the DATA already received (the request is
    /// then malformed, §4.1.2).
    pub fn declare_cl(&mut self, v: &[u8]) -> (ok: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).seen() == old(self).seen(),
            final(self).content() == old(self).content(),
            final(self).is_ended() == old(self).is_ended(),
            ok ==> verilith_http::spec::content_length_value(v@) is Some
                && final(self).cl_s() == verilith_http::spec::content_length_value(v@)
                && (old(self).cl_s() is Some ==> old(self).cl_s() == final(self).cl_s()),
    {
        if self.dead || self.ended {
            return false;
        }
        let n = match verilith_http::framing::content_length_exec(v) {
            Some(n) => n,
            None => return false,
        };
        self.len.declare(n)
    }

    /// Reads on from `input[*at..]`, which (with `fin`, the end of the
    /// stream) is what follows the bytes given before; moves `*at` past
    /// what it used.
    pub fn step(&mut self, input: &[u8], at: &mut usize, fin: bool) -> (a: Act)
        requires
            old(self).wf(),
            *old(at) <= input@.len(),
        ensures
            final(self).wf(),
            *old(at) <= *final(at) <= input@.len(),
            final(self).seen() == old(self).seen() + input@.subrange(*old(at) as int, *final(at) as int),
            old(self).is_ended() ==> a == Act::Done,
            a == Act::Ready ==> !old(self).is_ended() && final(self).ready(),
            a == Act::Need ==> *final(at) == input@.len(),
            a matches Act::Trailers(src) ==> match src {
                Src::Input(x, y) => *old(at) <= x <= y <= *final(at),
                Src::Buf(off) => off <= final(self).buf_v().len(),
            },
            a matches Act::Headers(src) ==> match src {
                Src::Input(x, y) => *old(at) <= x <= y <= *final(at)
                    && final(self).section() == input@.subrange(x as int, y as int),
                Src::Buf(off) => off <= final(self).buf_v().len()
                    && final(self).section() == final(self).buf_v().skip(off as int),
            },
    {
        if self.ended {
            proof { assert(input@.subrange(*at as int, *at as int) =~= Seq::<u8>::empty()); }
            return Act::Done;
        }
        if self.dead {
            proof { assert(input@.subrange(*at as int, *at as int) =~= Seq::<u8>::empty()); }
            return Act::Close(H3_INTERNAL_ERROR);
        }
        let ghost s0 = self.r.seen();
        let ghost at_start = *at;
        proof { assert(input@.subrange(at_start as int, at_start as int) =~= Seq::<u8>::empty()); assert(s0 + Seq::<u8>::empty() =~= s0); }
        loop
            invariant
                self.wf(),
                !self.ended,
                !self.dead,
                at_start == *old(at),
                !old(self).is_ended(),
                s0 == old(self).seen(),
                at_start <= *at <= input@.len(),
                self.r.seen() == s0 + input@.subrange(at_start as int, *at as int),
            decreases input@.len() - *at,
        {
            let at0 = *at;
            let rest = slice_subrange(input, at0, input.len());
            let ghost o = self.r;
            let (ev, used) = self.r.next(rest, fin);
            *at = at0 + used;
            proof {
                assert(rest@.take(used as int) =~= input@.subrange(at0 as int, *at as int));
                assert(input@.subrange(at_start as int, *at as int) =~= input@.subrange(at_start as int, at0 as int) + input@.subrange(at0 as int, *at as int));
                assert(self.r.seen() =~= s0 + input@.subrange(at_start as int, *at as int));
            }
            match ev {
                Event::Need => {
                    assert(used == rest@.len());
                    return Act::Need;
                },
                Event::End => {
                    if !self.got_headers {
                        // Not reached: a request stream may end only after
                        // its HEADERS (§4.1).
                        self.dead = true;
                        return Act::Malformed;
                    }
                    if !self.len.complete() {
                        // Less DATA than the Content-Length.
                        self.dead = true;
                        return Act::Malformed;
                    }
                    self.ended = true;
                    return Act::Ready;
                },
                Event::Error(c) => {
                    self.dead = true;
                    return Act::Close(c);
                },
                Event::Headers(src) => {
                    if !self.got_headers {
                        self.got_headers = true;
                        self.head = Ghost(src_view(src, rest@, self.r.buf_v()));
                        proof {
                            assert(self.r.events() == o.events().push(ev_view(ev, rest@, self.r.buf_v())));
                            assert(self.r.events()[0] == Ev::Headers(self.head@));
                        }
                        return Act::Headers(match src {
                            Src::Input(x, y) => {
                                proof {
                                    assert(rest@.subrange(x as int, y as int) =~= input@.subrange(at0 + x, at0 + y));
                                }
                                Src::Input(at0 + x, at0 + y)
                            },
                            Src::Buf(off) => Src::Buf(off),
                        });
                    }
                    // A second HEADERS frame is the trailers (the reader
                    // bounds its size, and no frame may follow it).
                    proof {
                        assert(self.r.events() == o.events().push(ev_view(ev, rest@, self.r.buf_v())));
                        assert(self.r.events()[0] == o.events()[0]);
                    }
                    return Act::Trailers(match src {
                        Src::Input(x, y) => Src::Input(at0 + x, at0 + y),
                        Src::Buf(off) => Src::Buf(off),
                    });
                },
                Event::Data(x, y) => {
                    let n = y - x;
                    let ghost d0 = self.data@;
                    self.data = Ghost(d0 + rest@.subrange(x as int, y as int));
                    if !self.len.add(n as u64) {
                        // More DATA than the Content-Length (or than
                        // 2^64 - 1 bytes).
                        self.dead = true;
                        return Act::Malformed;
                    }
                    if n > self.max_body - self.body.len() {
                        self.too_big = true;
                    } else if !self.too_big {
                        let ghost b0 = self.body@;
                        extend(&mut self.body, slice_subrange(rest, x, y));
                    }
                },
                _ => {
                    // Not reached: a request stream reports nothing else.
                    self.dead = true;
                    return Act::Close(H3_FRAME_UNEXPECTED);
                },
            }
        }
    }
}

// ---------------------------------------------------------------------
// A unidirectional stream the peer opened.

/// What [`Uni3::step`] asks of its caller.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UAct {
    /// Nothing to do until more arrives.
    Need,
    /// `input[from..]` is QPACK instructions, for the encoder stream's or
    /// decoder stream's instruction reader (`kind()`).
    Raw(usize),
    /// A connection error, with this code.
    Close(u64),
    /// A stream of a type we do not know (§6.2.3): stop reading it
    /// (H3_STREAM_CREATION_ERROR) and forget it.
    Discard,
}

/// A unidirectional stream at the server: the control stream (its frames
/// read by verilith-h3), a QPACK stream, or one of an unknown type.
pub struct Uni3 {
    r: Reader,
    kind: Option<UniKind>,
    /// Past the stream type of a QPACK or unknown stream.
    raw: bool,
    dead: bool,
}

/// The reason a step may close the connection: the verified reader's
/// error for the stream (§6.2.1, §7), opening a second critical stream
/// (§6.2.1, RFC 9204 §4.2), or a critical stream ending (§6.2.1).
pub open spec fn uni_close_ok(lim: nat, seen_bytes: Seq<u8>, open: UniSeen, kind: Option<UniKind>, fin: bool, c: u64) -> bool {
    ||| run(true, lim, seen_bytes, start(true, true)).tail == Tail::Fail(c)
    ||| end_of(true, lim, seen_bytes, start(true, true)) == Err::<(), u64>(c)
    ||| (kind is Some && uni_open(open, kind->Some_0) == Err::<UniSeen, u64>(c))
    ||| (fin && kind is Some && uni_closed(kind->Some_0) == Err::<(), u64>(c))
    ||| c == H3_INTERNAL_ERROR
}

impl Uni3 {
    pub closed spec fn seen(&self) -> Seq<u8> {
        self.r.seen()
    }

    pub closed spec fn limit(&self) -> nat {
        self.r.lim()
    }

    pub closed spec fn kind_s(&self) -> Option<UniKind> {
        self.kind
    }

    pub closed spec fn is_raw(&self) -> bool {
        self.raw
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.r.wf()
        &&& self.r.is_server()
        &&& self.r.st_start() == start(true, true)
        &&& !self.dead ==> {
            &&& (self.kind is None ==> self.r.events().len() == 0)
            &&& (self.kind is Some ==> self.r.events().len() > 0
                && self.r.events()[0] is StreamType && uni_kind(self.r.events()[0]->StreamType_0 as nat) == self.kind->Some_0)
        }
        &&& self.raw ==> {
            &&& self.kind is Some
            &&& (self.kind->Some_0 is QpackEncoder || self.kind->Some_0 is QpackDecoder || self.kind->Some_0 is Other)
            &&& run(true, self.r.lim(), self.r.seen(), start(true, true)).tail is Handoff
        }
    }

    pub fn new(max_field_section: u64) -> (r: Uni3)
        ensures
            r.wf(),
            r.seen() == Seq::<u8>::empty(),
            r.kind_s() is None,
            !r.is_raw(),
    {
        Uni3 { r: Reader::new_uni(true, max_field_section), kind: None, raw: false, dead: false }
    }

    pub fn kind(&self) -> (r: Option<UniKind>)
        ensures
            r == self.kind_s(),
    {
        self.kind
    }

    /// Reads on with `input`, the stream's next bytes (`fin`: its last, or
    /// the stream was reset); `open` is the critical streams the peer has
    /// opened, updated when this one's type arrives.
    pub fn step(&mut self, open: &mut UniSeen, input: &[u8], fin: bool) -> (a: UAct)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).limit() == old(self).limit(),
            // The stream type: the critical streams opened are updated by
            // the rule of §6.2.1 once, when it arrives.
            *final(open) == *old(open) || (old(self).kind_s() is None && final(self).kind_s() is Some
                && uni_open(*old(open), final(self).kind_s()->Some_0) == Ok::<UniSeen, u64>(*final(open))),
            old(self).kind_s() is Some ==> final(self).kind_s() == old(self).kind_s(),
            a matches UAct::Raw(from) ==> {
                &&& from <= input@.len()
                &&& !fin
                &&& final(self).is_raw()
                &&& final(self).kind_s() is Some
                &&& (final(self).kind_s()->Some_0 is QpackEncoder || final(self).kind_s()->Some_0 is QpackDecoder)
                // QPACK gets exactly the bytes the verified reader did not
                // take (it stopped at the end of the stream type).
                &&& final(self).seen() == old(self).seen() + input@.take(from as int)
            },
            a is Discard ==> final(self).kind_s() == Some(UniKind::Other),
            a matches UAct::Close(c) ==> uni_close_ok(final(self).limit(), final(self).seen(), *old(open), final(self).kind_s(), fin, c),
    {
        if self.dead {
            return UAct::Close(H3_INTERNAL_ERROR);
        }
        let ghost s0 = self.r.seen();
        let mut at: usize = 0;
        let mut spun = false;
        proof { assert(input@.take(0) =~= Seq::<u8>::empty()); assert(s0 + Seq::<u8>::empty() =~= s0); }
        if !self.raw {
        loop
            invariant_except_break
                !self.raw,
            invariant
                self.wf(),
                !self.dead,
                s0 == old(self).seen(),
                at <= input@.len(),
                self.r.seen() == s0 + input@.take(at as int),
                self.r.lim() == old(self).limit(),
                *open == *old(open) || (old(self).kind_s() is None && self.kind is Some
                    && uni_open(*old(open), self.kind->Some_0) == Ok::<UniSeen, u64>(*open)),
                old(self).kind_s() is Some ==> self.kind == old(self).kind_s(),
            ensures
                self.raw,
            decreases (input@.len() - at) * 2 + if spun { 0int } else { 1int },
        {
            let at0 = at;
            let rest = slice_subrange(input, at0, input.len());
            let ghost o = self.r;
            let (ev, used) = self.r.next(rest, fin);
            at = at0 + used;
            proof {
                assert(rest@.take(used as int) =~= input@.subrange(at0 as int, at as int));
                assert(input@.take(at as int) =~= input@.take(at0 as int) + input@.subrange(at0 as int, at as int));
                assert(self.r.seen() =~= s0 + input@.take(at as int));
            }
            match ev {
                Event::Need | Event::End => {
                    return UAct::Need;
                },
                Event::Error(c) => {
                    self.dead = true;
                    return UAct::Close(c);
                },
                Event::StreamType(t) => {
                    if self.kind.is_some() {
                        // Not reached: the type comes first, once.
                        self.dead = true;
                        return UAct::Close(H3_INTERNAL_ERROR);
                    }
                    let k = verilith_h3::frame::uni_kind_of(t);
                    proof {
                        assert(self.r.events() == o.events().push(ev_view(ev, rest@, self.r.buf_v())));
                    }
                    self.kind = Some(k);
                    match verilith_h3::frame::uni_open_x(*open, k) {
                        Ok(s) => {
                            *open = s;
                        },
                        Err(c) => {
                            self.dead = true;
                            return UAct::Close(c);
                        },
                    }
                },
                Event::Handoff => {
                    match self.kind {
                        Some(k) => {
                            if matches!(k, UniKind::Control | UniKind::Push) {
                                // Not reached: these are framed.
                                self.dead = true;
                                return UAct::Close(H3_INTERNAL_ERROR);
                            }
                        },
                        None => {
                            self.dead = true;
                            return UAct::Close(H3_INTERNAL_ERROR);
                        },
                    }
                    self.raw = true;
                    break;
                },
                Event::Data(..) => {
                    // Not reached: no DATA on a control stream (§7.2.1).
                    self.dead = true;
                    return UAct::Close(H3_INTERNAL_ERROR);
                },
                _ => {
                    // SETTINGS: ours use no dynamic table and no
                    // extensions, so nothing the client says changes what
                    // we send. GOAWAY (a push ID, §5.2), MAX_PUSH_ID,
                    // CANCEL_PUSH: we do not push. Every one is checked by
                    // the reader (order, IDs, values).
                    if self.kind.is_none() {
                        self.dead = true;
                        return UAct::Close(H3_INTERNAL_ERROR);
                    }
                    proof {
                        assert(self.r.events() == o.events().push(ev_view(ev, rest@, self.r.buf_v())));
                        assert(self.r.events()[0] == o.events()[0]);
                    }
                },
            }
            // Not reached twice in a row: a call that uses no input
            // reports a frame whose last byte came before.
            if used == 0 {
                if spun {
                    self.dead = true;
                    return UAct::Close(H3_INTERNAL_ERROR);
                }
                spun = true;
            } else {
                spun = false;
            }
        }
        }
        match self.kind {
            Some(UniKind::QpackEncoder) | Some(UniKind::QpackDecoder) => {
                if fin {
                    // A QPACK stream must not end (RFC 9204 §4.2).
                    return UAct::Close(H3_CLOSED_CRITICAL_STREAM);
                }
                assert(at <= input@.len());
                assert(self.raw);
                assert(self.r.seen() == old(self).seen() + input@.take(at as int));
                UAct::Raw(at)
            },
            Some(UniKind::Other) => UAct::Discard,
            _ => {
                self.dead = true;
                UAct::Close(H3_INTERNAL_ERROR)
            },
        }
    }
}

// ---------------------------------------------------------------------
// The flood budget.

/// Work the peer can make us do without completing requests: each
/// request stream it abandons (reset before its end, or refused for its
/// size or form) costs one unit; each complete request earns
/// `per_request`. The connection is closed (H3_EXCESSIVE_LOAD) when the
/// cost passes `base` plus what was earned: so over a connection's life,
/// `abandoned <= base + per_request * completed`.
pub struct Budget {
    cost: u64,
    allowed: u64,
    per_request: u64,
    base: Ghost<nat>,
    completed: Ghost<nat>,
    abandoned: Ghost<nat>,
}

impl Budget {
    pub closed spec fn inv(&self) -> bool {
        &&& self.cost as nat == self.abandoned@
        &&& self.allowed as nat <= self.base@ + self.per_request * self.completed@
        &&& self.cost <= self.allowed
    }

    pub closed spec fn abandoned(&self) -> nat {
        self.abandoned@
    }

    pub closed spec fn completed(&self) -> nat {
        self.completed@
    }

    pub closed spec fn base(&self) -> nat {
        self.base@
    }

    pub closed spec fn per(&self) -> nat {
        self.per_request as nat
    }

    pub fn new(base: u64, per_request: u64) -> (r: Budget)
        ensures
            r.inv(),
            r.abandoned() == 0,
            r.completed() == 0,
            r.base() == base,
            r.per() == per_request,
    {
        Budget { cost: 0, allowed: base, per_request, base: Ghost(base as nat), completed: Ghost(0), abandoned: Ghost(0) }
    }

    /// A request was completed.
    pub fn earn(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).completed() == old(self).completed() + 1,
            final(self).abandoned() == old(self).abandoned(),
            final(self).base() == old(self).base(),
            final(self).per() == old(self).per(),
    {
        proof {
            assert(self.per_request * (self.completed@ + 1) == self.per_request * self.completed@ + self.per_request) by (nonlinear_arith);
        }
        self.allowed = self.allowed.saturating_add(self.per_request);
        self.completed = Ghost(self.completed@ + 1);
    }

    /// A request stream was abandoned; false when that is over the budget
    /// (close the connection).
    pub fn spend(&mut self) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            ok ==> final(self).inv() && final(self).abandoned() == old(self).abandoned() + 1,
            !ok ==> *final(self) == *old(self),
            final(self).completed() == old(self).completed(),
            final(self).base() == old(self).base(),
            final(self).per() == old(self).per(),
    {
        if self.cost >= self.allowed {
            return false;
        }
        self.cost = self.cost + 1;
        self.abandoned = Ghost(self.abandoned@ + 1);
        true
    }
}

/// The theorem the budget gives: requests abandoned are at most `base`
/// plus `per_request` per request completed.
pub proof fn lemma_budget(b: &Budget)
    requires
        b.inv(),
    ensures
        b.abandoned() <= b.base() + b.per() * b.completed(),
{
}

} // verus!
