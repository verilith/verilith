//! The encoders, proven to write `spec::frame_enc`, and the round trip:
//! `frame_dec(frame_enc(f) + rest)` is `f`, for every frame that can be
//! sent.
use crate::frame::*;
use crate::spec::*;
use crate::varint::*;
use vstd::prelude::*;

verus! {

/// `n` is `o` with `e` written at `at..r`.
pub open spec fn wrote(o: Seq<u8>, n: Seq<u8>, at: int, r: int, e: Seq<u8>) -> bool {
    &&& 0 <= at <= r <= o.len()
    &&& n.len() == o.len()
    &&& r - at == e.len()
    &&& n.subrange(at, r) == e
    &&& n.subrange(0, at) == o.subrange(0, at)
    &&& n.subrange(r, n.len() as int) == o.subrange(r, o.len() as int)
}

pub proof fn lemma_wrote_seq(o: Seq<u8>, m: Seq<u8>, n: Seq<u8>, at: int, r1: int, r2: int, e1: Seq<u8>, e2: Seq<u8>)
    requires
        wrote(o, m, at, r1, e1),
        wrote(m, n, r1, r2, e2),
    ensures
        wrote(o, n, at, r2, e1 + e2),
{
    assert(n.subrange(at, r1) =~= m.subrange(at, r1)) by {
        assert forall|i: int| 0 <= i < r1 - at implies n.subrange(at, r1)[i] == m.subrange(at, r1)[i] by {
            assert(n.subrange(0, r1)[at + i] == m.subrange(0, r1)[at + i]);
        }
    }
    assert(n.subrange(at, r2) =~= n.subrange(at, r1) + n.subrange(r1, r2));
    assert(n.subrange(0, at) =~= m.subrange(0, r1).subrange(0, at));
    assert(m.subrange(0, at) =~= m.subrange(0, r1).subrange(0, at));
    assert(n.subrange(r2, n.len() as int) =~= m.subrange(r1, m.len() as int).subrange(r2 - r1, m.len() - r1));
    assert(o.subrange(r2, o.len() as int) =~= o.subrange(r1, o.len() as int).subrange(r2 - r1, o.len() - r1));
}

/// Writes a varint, as `wrote` states it.
#[inline(always)]
pub fn put(out: &mut [u8], at: usize, v: u64) -> (r: usize)
    requires
        v <= MAX_VARINT,
        at + var_size(v as nat) <= old(out)@.len(),
    ensures
        wrote(old(out)@, final(out)@, at as int, r as int, var_enc(v as nat)),
{
    proof {
        lemma_var_enc(v as nat);
    }
    put_var(out, at, v)
}

/// The length of a frame header for type `t` and payload length `len`.
#[inline(always)]
pub fn header_size(t: u64, len: u64) -> (r: usize)
    ensures
        r == var_size(t as nat) + var_size(len as nat),
        r <= 16,
{
    var_size_of(t) + var_size_of(len)
}

/// Writes the header of a frame of type `t` with a `len`-byte payload (for
/// DATA and HEADERS, whose payload the caller then writes or sends from
/// where it is).
#[inline(always)]
pub fn put_header(out: &mut [u8], at: usize, t: u64, len: u64) -> (r: usize)
    requires
        t <= MAX_VARINT,
        len <= MAX_VARINT,
        at + var_size(t as nat) + var_size(len as nat) <= old(out)@.len(),
    ensures
        wrote(old(out)@, final(out)@, at as int, r as int, var_enc(t as nat) + var_enc(len as nat)),
{
    proof {
        lemma_var_enc(t as nat);
        lemma_var_enc(len as nat);
    }
    let ghost o = out@;
    let r1 = put(out, at, t);
    let ghost m = out@;
    let r2 = put(out, r1, len);
    proof {
        lemma_wrote_seq(o, m, out@, at as int, r1 as int, r2 as int, var_enc(t as nat), var_enc(len as nat));
    }
    r2
}

#[inline(always)]
fn setting_size(v: Option<u64>, idsize: usize) -> (r: usize)
    requires
        idsize <= 8,
        v matches Some(x) ==> x <= MAX_VARINT,
    ensures
        r <= 16,
        match v {
            Some(x) => r == idsize + var_size(x as nat),
            None => r == 0,
        },
{
    match v {
        Some(x) => idsize + var_size_of(x),
        None => 0,
    }
}

#[inline(always)]
fn put_setting(out: &mut [u8], at: usize, id: u64, v: Option<u64>) -> (r: usize)
    requires
        id <= 63,
        v matches Some(x) ==> x <= MAX_VARINT,
        at + setting_enc(id as nat, v).len() <= old(out)@.len(),
    ensures
        wrote(old(out)@, final(out)@, at as int, r as int, setting_enc(id as nat, v)),
{
    proof {
        lemma_var_enc(id as nat);
        if let Some(x) = v {
            lemma_var_enc(x as nat);
        }
    }
    match v {
        Some(x) => put_header(out, at, id, x),
        None => {
            proof {
                assert(out@.subrange(at as int, at as int) =~= Seq::<u8>::empty());
            }
            at
        },
    }
}

/// The length of SETTINGS' payload for `s`.
pub fn settings_size(s: &Settings) -> (r: usize)
    requires
        settings_ok(*s),
    ensures
        r == settings_enc(*s).len(),
        r <= 80,
{
    proof {
        lemma_var_enc(1);
        lemma_var_enc(6);
        lemma_var_enc(7);
        lemma_var_enc(8);
        lemma_var_enc(0x33);
        reveal_with_fuel(be_enc, 2);
        if let Some(x) = s.qpack_max_table_capacity { lemma_var_enc(x as nat); }
        if let Some(x) = s.max_field_section_size { lemma_var_enc(x as nat); }
        if let Some(x) = s.qpack_blocked_streams { lemma_var_enc(x as nat); }
        if let Some(x) = s.enable_connect_protocol { lemma_var_enc(x as nat); }
        if let Some(x) = s.h3_datagram { lemma_var_enc(x as nat); }
    }
    setting_size(s.qpack_max_table_capacity, 1) + setting_size(s.max_field_section_size, 1) + setting_size(
        s.qpack_blocked_streams,
        1,
    ) + setting_size(s.enable_connect_protocol, 1) + setting_size(s.h3_datagram, 1)
}

/// Writes a SETTINGS frame for `s`.
#[verifier::rlimit(60)]
pub fn put_settings(out: &mut [u8], at: usize, s: &Settings) -> (r: usize)
    requires
        settings_ok(*s),
        at + frame_enc(Frame::Settings(*s)).len() <= old(out)@.len(),
    ensures
        wrote(old(out)@, final(out)@, at as int, r as int, frame_enc(Frame::Settings(*s))),
{
    let n = settings_size(s);
    proof {
        lemma_var_enc(SETTINGS as nat);
        lemma_var_enc(n as nat);
    }
    let ghost o0 = out@;
    let p = put_header(out, at, SETTINGS, n as u64);
    let ghost o1 = out@;
    let p1 = put_setting(out, p, SETTINGS_QPACK_MAX_TABLE_CAPACITY, s.qpack_max_table_capacity);
    let ghost o2 = out@;
    let p2 = put_setting(out, p1, SETTINGS_MAX_FIELD_SECTION_SIZE, s.max_field_section_size);
    let ghost o3 = out@;
    let p3 = put_setting(out, p2, SETTINGS_QPACK_BLOCKED_STREAMS, s.qpack_blocked_streams);
    let ghost o4 = out@;
    let p4 = put_setting(out, p3, SETTINGS_ENABLE_CONNECT_PROTOCOL, s.enable_connect_protocol);
    let ghost o5 = out@;
    let p5 = put_setting(out, p4, SETTINGS_H3_DATAGRAM, s.h3_datagram);
    proof {
        let h = var_enc(SETTINGS as nat) + var_enc(n as nat);
        let e1 = setting_enc(SETTINGS_QPACK_MAX_TABLE_CAPACITY as nat, s.qpack_max_table_capacity);
        let e2 = setting_enc(SETTINGS_MAX_FIELD_SECTION_SIZE as nat, s.max_field_section_size);
        let e3 = setting_enc(SETTINGS_QPACK_BLOCKED_STREAMS as nat, s.qpack_blocked_streams);
        let e4 = setting_enc(SETTINGS_ENABLE_CONNECT_PROTOCOL as nat, s.enable_connect_protocol);
        let e5 = setting_enc(SETTINGS_H3_DATAGRAM as nat, s.h3_datagram);
        lemma_wrote_seq(o0, o1, o2, at as int, p as int, p1 as int, h, e1);
        lemma_wrote_seq(o0, o2, o3, at as int, p1 as int, p2 as int, h + e1, e2);
        lemma_wrote_seq(o0, o3, o4, at as int, p2 as int, p3 as int, h + e1 + e2, e3);
        lemma_wrote_seq(o0, o4, o5, at as int, p3 as int, p4 as int, h + e1 + e2 + e3, e4);
        lemma_wrote_seq(o0, o5, out@, at as int, p4 as int, p5 as int, h + e1 + e2 + e3 + e4, e5);
        assert(h + e1 + e2 + e3 + e4 + e5 =~= frame_enc(Frame::Settings(*s)));
    }
    p5
}

/// Writes a CANCEL_PUSH, GOAWAY or MAX_PUSH_ID frame (`t`) carrying `v`.
pub fn put_id_frame(out: &mut [u8], at: usize, t: u64, v: u64) -> (r: usize)
    requires
        t == CANCEL_PUSH || t == GOAWAY || t == MAX_PUSH_ID,
        v <= MAX_VARINT,
        at + 2 + var_size(v as nat) <= old(out)@.len(),
    ensures
        wrote(old(out)@, final(out)@, at as int, r as int, frame_enc(
            if t == CANCEL_PUSH {
                Frame::CancelPush(v as nat)
            } else if t == GOAWAY {
                Frame::Goaway(v as nat)
            } else {
                Frame::MaxPushId(v as nat)
            },
        )),
        r == at + 2 + var_size(v as nat),
{
    let n = var_size_of(v);
    proof {
        lemma_var_enc(t as nat);
        lemma_var_enc(n as nat);
        lemma_var_enc(v as nat);
        reveal_with_fuel(be_enc, 2);
    }
    let ghost o0 = out@;
    let p = put_header(out, at, t, n as u64);
    let ghost o1 = out@;
    let p2 = put(out, p, v);
    proof {
        lemma_wrote_seq(o0, o1, out@, at as int, p as int, p2 as int, var_enc(t as nat) + var_enc(n as nat), var_enc(v as nat));
    }
    p2
}

/// Writes a PUSH_PROMISE frame's header and push ID, for a field section
/// of `section` bytes that the caller writes next.
pub fn put_push_promise_head(out: &mut [u8], at: usize, id: u64, section: u64) -> (r: usize)
    requires
        id <= MAX_VARINT,
        section + 8 <= MAX_VARINT,
        at + 1 + var_size((var_size(id as nat) + section) as nat) + var_size(id as nat) <= old(out)@.len(),
    ensures
        wrote(old(out)@, final(out)@, at as int, r as int, var_enc(PUSH_PROMISE as nat) + var_enc((var_size(id as nat) + section) as nat) + var_enc(id as nat)),
        forall|p: Seq<u8>| p.len() == section ==> #[trigger] frame_enc(Frame::PushPromise(id as nat, p)) == var_enc(PUSH_PROMISE as nat) + var_enc((var_size(id as nat) + section) as nat) + var_enc(id as nat) + p,
{
    let n = var_size_of(id) as u64 + section;
    proof {
        lemma_var_enc(PUSH_PROMISE as nat);
        lemma_var_enc(n as nat);
        lemma_var_enc(id as nat);
        assert forall|p: Seq<u8>| p.len() == section implies #[trigger] frame_enc(Frame::PushPromise(id as nat, p)) == var_enc(PUSH_PROMISE as nat) + var_enc((var_size(id as nat) + section) as nat) + var_enc(id as nat) + p by {
            assert(payload_enc(Frame::PushPromise(id as nat, p)).len() == n);
            assert(var_enc(PUSH_PROMISE as nat) + var_enc(n as nat) + (var_enc(id as nat) + p) =~= var_enc(PUSH_PROMISE as nat) + var_enc(n as nat) + var_enc(id as nat) + p);
        }
    }
    let ghost o0 = out@;
    let p = put_header(out, at, PUSH_PROMISE, n);
    let ghost o1 = out@;
    let p2 = put(out, p, id);
    proof {
        lemma_wrote_seq(o0, o1, out@, at as int, p as int, p2 as int, var_enc(PUSH_PROMISE as nat) + var_enc(n as nat), var_enc(id as nat));
    }
    p2
}

// ---------------------------------------------------------------------------
// The round trip
// ---------------------------------------------------------------------------

/// A varint reads back, with anything after it.
pub proof fn lemma_var_rt(v: nat, rest: Seq<u8>)
    requires
        v <= MAX_VARINT,
    ensures
        var_dec(var_enc(v) + rest) == Var::Ok(v, var_size(v)),
{
    lemma_var_enc(v);
    let e = var_enc(v);
    assert((e + rest).take(e.len() as int) =~= e.take(e.len() as int));
    lemma_var_ext(e, e + rest);
}

/// A frame header reads back.
pub proof fn lemma_hdr_rt(t: nat, len: nat, rest: Seq<u8>)
    requires
        t <= MAX_VARINT,
        len <= MAX_VARINT,
    ensures
        hdr_dec(var_enc(t) + var_enc(len) + rest) == Hdr::Ok(t, len, var_size(t) + var_size(len)),
{
    let s = var_enc(t) + var_enc(len) + rest;
    lemma_var_enc(t);
    assert(s =~= var_enc(t) + (var_enc(len) + rest));
    lemma_var_rt(t, var_enc(len) + rest);
    assert(s.skip(var_size(t) as int) =~= var_enc(len) + rest);
    lemma_var_rt(len, rest);
}

proof fn lemma_setting_rt(acc: Settings, id: nat, v: Option<u64>, rest: Seq<u8>, acc2: Settings)
    requires
        id <= 63,
        v matches Some(x) ==> x <= MAX_VARINT,
        v is None ==> acc2 == acc,
        v matches Some(x) ==> setting(acc, id, x as nat) == Ok::<Settings, u64>(acc2),
    ensures
        settings_from(setting_enc(id, v) + rest, acc) == settings_from(rest, acc2),
{
    if let Some(x) = v {
        let s = setting_enc(id, v) + rest;
        lemma_var_enc(id);
        lemma_var_enc(x as nat);
        assert(s =~= var_enc(id) + (var_enc(x as nat) + rest));
        lemma_var_rt(id, var_enc(x as nat) + rest);
        assert(s.skip(var_size(id) as int) =~= var_enc(x as nat) + rest);
        lemma_var_rt(x as nat, rest);
        assert(s.skip((var_size(id) + var_size(x as nat)) as int) =~= rest);
    } else {
        assert(setting_enc(id, v) + rest =~= rest);
    }
}

/// SETTINGS' payload reads back.
pub proof fn lemma_settings_rt(s: Settings)
    requires
        settings_ok(s),
    ensures
        settings_dec(settings_enc(s)) == Ok::<Settings, u64>(s),
{
    let e = Seq::<u8>::empty();
    let a0 = no_settings();
    let a1 = Settings { qpack_max_table_capacity: s.qpack_max_table_capacity, ..a0 };
    let a2 = Settings { max_field_section_size: s.max_field_section_size, ..a1 };
    let a3 = Settings { qpack_blocked_streams: s.qpack_blocked_streams, ..a2 };
    let a4 = Settings { enable_connect_protocol: s.enable_connect_protocol, ..a3 };
    let e1 = setting_enc(1, s.qpack_max_table_capacity);
    let e2 = setting_enc(6, s.max_field_section_size);
    let e3 = setting_enc(7, s.qpack_blocked_streams);
    let e4 = setting_enc(8, s.enable_connect_protocol);
    let e5 = setting_enc(0x33, s.h3_datagram);
    assert(settings_enc(s) =~= e1 + (e2 + (e3 + (e4 + (e5 + e)))));
    lemma_setting_rt(a3, 8, s.enable_connect_protocol, e5 + e, a4);
    lemma_setting_rt(a4, 0x33, s.h3_datagram, e, s);
    lemma_setting_rt(a2, 7, s.qpack_blocked_streams, e4 + (e5 + e), a3);
    lemma_setting_rt(a1, 6, s.max_field_section_size, e3 + (e4 + (e5 + e)), a2);
    lemma_setting_rt(a0, 1, s.qpack_max_table_capacity, e2 + (e3 + (e4 + (e5 + e))), a1);
}

/// The round trip: every frame that can be sent reads back as itself (a
/// frame of a reserved HTTP/2 type reads back as `Other`, which is what it
/// was built as), and the bytes after it are not read.
pub proof fn lemma_frame_rt(f: Frame, rest: Seq<u8>)
    requires
        frame_ok(f),
    ensures
        frame_dec(frame_enc(f) + rest) == Some((f, frame_enc(f).len())),
{
    let t = frame_type(f);
    let p = payload_enc(f);
    let s = frame_enc(f) + rest;
    assert(t <= MAX_VARINT);
    lemma_var_enc(t);
    lemma_var_enc(p.len());
    assert(s =~= var_enc(t) + var_enc(p.len()) + (p + rest));
    lemma_hdr_rt(t, p.len(), p + rest);
    let h = var_size(t) + var_size(p.len());
    assert(s.subrange(h as int, (h + p.len()) as int) =~= p);
    match f {
        Frame::CancelPush(v) | Frame::Goaway(v) | Frame::MaxPushId(v) => {
            lemma_var_enc(v);
        },
        Frame::Settings(x) => {
            lemma_settings_rt(x);
        },
        Frame::PushPromise(id, q) => {
            lemma_var_rt(id, q);
            lemma_var_enc(id);
            assert(p.skip(var_size(id) as int) =~= q);
        },
        _ => {},
    }
}

/// What the reader reports for frame `f`.
pub open spec fn frame_ev(f: Frame) -> Seq<Ev> {
    match f {
        Frame::Headers(p) => seq![Ev::Headers(p)],
        Frame::PushPromise(id, p) => seq![Ev::PushPromise(id as u64, p)],
        Frame::Settings(x) => seq![Ev::Settings(x)],
        Frame::CancelPush(v) => seq![Ev::CancelPush(v as u64)],
        Frame::Goaway(v) => seq![Ev::Goaway(v as u64)],
        Frame::MaxPushId(v) => seq![Ev::MaxPushId(v as u64)],
        Frame::Data(_) | Frame::Other(..) => seq![],
    }
}

/// The DATA payload it carries.
pub open spec fn frame_data(f: Frame) -> Seq<u8> {
    match f {
        Frame::Data(p) => p,
        _ => seq![],
    }
}

/// The round trip through the stream reader: an encoded frame, in a state
/// where its type is allowed, is one unit of exactly its length that
/// reports exactly the frame. The one exception is the ID rules (§7.2.3,
/// §7.2.6, §7.2.7), which can reject a CANCEL_PUSH, GOAWAY or MAX_PUSH_ID
/// by its value.
pub proof fn lemma_unit_rt(server: bool, limit: nat, o: Order, f: Frame, rest: Seq<u8>)
    requires
        frame_ok(f),
        accept(o, server, limit, frame_type(f), payload_enc(f).len()) is Ok,
    ensures
        ({
            let u = unit(server, limit, frame_enc(f) + rest, RSt::Frames(o));
            &&& !(u is Incomplete) && !(u is Handoff)
            &&& u is Fail ==> (f is CancelPush || f is Goaway || f is MaxPushId)
            &&& u matches Unit::Done(_, n, ev, d) ==> n == frame_enc(f).len() && ev == frame_ev(f) && d == frame_data(f)
        }),
{
    let t = frame_type(f);
    let p = payload_enc(f);
    let s = frame_enc(f) + rest;
    lemma_frame_rt(f, rest);
    lemma_var_enc(t);
    lemma_var_enc(p.len());
    assert(s =~= var_enc(t) + var_enc(p.len()) + (p + rest));
    lemma_hdr_rt(t, p.len(), p + rest);
    let h = var_size(t) + var_size(p.len());
    assert(s.subrange(h as int, (h + p.len()) as int) =~= p);
    match f {
        Frame::CancelPush(v) | Frame::Goaway(v) | Frame::MaxPushId(v) => {
            lemma_var_enc(v);
        },
        Frame::Settings(x) => {
            lemma_settings_rt(x);
        },
        Frame::PushPromise(id, q) => {
            lemma_var_rt(id, q);
            lemma_var_enc(id);
            assert(p.skip(var_size(id) as int) =~= q);
        },
        _ => {},
    }
}

// The checked writers: the public API. Each checks its arguments and the
// room in `out` and returns `None` (writing nothing) when either is
// wrong, so plain Rust callers cannot reach the unchecked `put_*`.

/// Whether `out[at..]` has room for `n` bytes.
#[inline(always)]
fn room(out: &[u8], at: usize, n: usize) -> (r: bool)
    ensures
        r == (at + n <= out@.len()),
{
    at <= out.len() && n <= out.len() - at
}

/// Writes varint `v` at `out[at..]`; returns its end, or `None` if `v` is
/// over 2^62 - 1 or does not fit.
#[inline]
pub fn write_var(out: &mut [u8], at: usize, v: u64) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> v <= MAX_VARINT && wrote(old(out)@, final(out)@, at as int, e as int, var_enc(v as nat)),
        r is None ==> final(out)@ == old(out)@,
{
    if v > MAX_VARINT || !room(out, at, var_size_of(v)) {
        return None;
    }
    Some(put(out, at, v))
}

/// Writes the header of a frame of type `t` whose payload is `len` bytes
/// (for DATA and HEADERS, whose payload the caller writes or sends next);
/// returns its end, or `None` if a value is over 2^62 - 1 or it does not
/// fit.
#[inline]
pub fn write_header(out: &mut [u8], at: usize, t: u64, len: u64) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> t <= MAX_VARINT && len <= MAX_VARINT && wrote(old(out)@, final(out)@, at as int, e as int, var_enc(t as nat) + var_enc(len as nat)),
        r is None ==> final(out)@ == old(out)@,
{
    if t > MAX_VARINT || len > MAX_VARINT || !room(out, at, header_size(t, len)) {
        return None;
    }
    Some(put_header(out, at, t, len))
}

/// The length of the SETTINGS frame for `s`, or `None` if a value is out
/// of range.
pub fn settings_frame_size(s: &Settings) -> (r: Option<usize>)
    ensures
        r matches Some(n) ==> settings_ok(*s) && n == frame_enc(Frame::Settings(*s)).len(),
        r is None ==> !settings_ok(*s),
{
    if !settings_valid(s) {
        return None;
    }
    let n = settings_size(s);
    proof {
        lemma_var_enc(SETTINGS as nat);
        lemma_var_enc(n as nat);
    }
    Some(header_size(SETTINGS, n as u64) + n)
}

/// Whether `x` is a value over `m`.
#[inline(always)]
fn over(x: Option<u64>, m: u64) -> (r: bool)
    ensures
        r == (x matches Some(v) && v > m),
{
    match x {
        Some(v) => v > m,
        None => false,
    }
}

/// `settings_ok`, in code.
#[inline]
fn settings_valid(s: &Settings) -> (r: bool)
    ensures
        r == settings_ok(*s),
{
    !(over(s.qpack_max_table_capacity, MAX_VARINT) || over(s.max_field_section_size, MAX_VARINT) || over(
        s.qpack_blocked_streams,
        MAX_VARINT,
    ) || over(s.enable_connect_protocol, 1) || over(s.h3_datagram, 1))
}

/// Writes the SETTINGS frame for `s`; returns its end, or `None` if a
/// value is out of range or it does not fit.
pub fn write_settings(out: &mut [u8], at: usize, s: &Settings) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> settings_ok(*s) && wrote(old(out)@, final(out)@, at as int, e as int, frame_enc(Frame::Settings(*s))),
        r is None ==> final(out)@ == old(out)@,
{
    match settings_frame_size(s) {
        None => None,
        Some(n) => {
            if !room(out, at, n) {
                return None;
            }
            Some(put_settings(out, at, s))
        },
    }
}

/// Writes a CANCEL_PUSH, GOAWAY or MAX_PUSH_ID frame (`t`) carrying `v`;
/// returns its end, or `None` if `t` is another type, `v` is over
/// 2^62 - 1, or it does not fit.
pub fn write_id_frame(out: &mut [u8], at: usize, t: u64, v: u64) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> (t == CANCEL_PUSH || t == GOAWAY || t == MAX_PUSH_ID) && v <= MAX_VARINT && wrote(old(out)@, final(out)@, at as int, e as int, frame_enc(
            if t == CANCEL_PUSH {
                Frame::CancelPush(v as nat)
            } else if t == GOAWAY {
                Frame::Goaway(v as nat)
            } else {
                Frame::MaxPushId(v as nat)
            },
        )),
        r is None ==> final(out)@ == old(out)@,
{
    if !(t == CANCEL_PUSH || t == GOAWAY || t == MAX_PUSH_ID) || v > MAX_VARINT {
        return None;
    }
    let n = var_size_of(v);
    if !room(out, at, 2 + n) {
        return None;
    }
    Some(put_id_frame(out, at, t, v))
}

/// Writes a PUSH_PROMISE frame's header and push ID, for a field section
/// of `section` bytes that the caller writes next; returns its end, or
/// `None` if a value is out of range or it does not fit.
pub fn write_push_promise_head(out: &mut [u8], at: usize, id: u64, section: u64) -> (r: Option<usize>)
    ensures
        r matches Some(e) ==> id <= MAX_VARINT && section + 8 <= MAX_VARINT && wrote(old(out)@, final(out)@, at as int, e as int, var_enc(PUSH_PROMISE as nat) + var_enc((var_size(id as nat) + section) as nat) + var_enc(id as nat)),
        r matches Some(e) ==> forall|p: Seq<u8>| p.len() == section ==> #[trigger] frame_enc(Frame::PushPromise(id as nat, p)) == var_enc(PUSH_PROMISE as nat) + var_enc((var_size(id as nat) + section) as nat) + var_enc(id as nat) + p,
        r is None ==> final(out)@ == old(out)@,
{
    if id > MAX_VARINT || section > MAX_VARINT - 8 {
        return None;
    }
    let n = var_size_of(id);
    let total = var_size_of(n as u64 + section);
    if !room(out, at, 1 + total + n) {
        return None;
    }
    Some(put_push_promise_head(out, at, id, section))
}

} // verus!
