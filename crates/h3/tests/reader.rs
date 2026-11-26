//! The reader on hand-built streams, whole and split at every byte.
use verilith_h3::spec::*;
use verilith_h3::{Event, Reader, Src};

fn var(v: u64) -> Vec<u8> {
    if v < 64 {
        vec![v as u8]
    } else if v < 16384 {
        vec![0x40 | (v >> 8) as u8, v as u8]
    } else if v < 1 << 30 {
        ((v as u32) | 0x8000_0000).to_be_bytes().to_vec()
    } else {
        (v | 0xc000_0000_0000_0000).to_be_bytes().to_vec()
    }
}

fn frame(t: u64, p: &[u8]) -> Vec<u8> {
    let mut v = var(t);
    v.extend(var(p.len() as u64));
    v.extend_from_slice(p);
    v
}

/// What a stream reports, with DATA merged, and how it ends.
#[derive(Debug, PartialEq, Clone)]
enum Out {
    Type(u64),
    PushId(u64),
    Data(Vec<u8>),
    Headers(Vec<u8>),
    PushPromise(u64, Vec<u8>),
    Settings(Settings),
    CancelPush(u64),
    Goaway(u64),
    MaxPushId(u64),
    End,
    Error(u64),
    Handoff,
}

fn src(r: &Reader, input: &[u8], s: Src) -> Vec<u8> {
    match s {
        Src::Input(a, b) => input[a..b].to_vec(),
        Src::Buf(off) => r.buffered()[off..].to_vec(),
    }
}

/// Feeds `pieces` in turn (the last with fin), collecting events.
fn feed(mut r: Reader, pieces: &[&[u8]]) -> Vec<Out> {
    let mut out: Vec<Out> = Vec::new();
    let mut push = |o: Out, out: &mut Vec<Out>| {
        if let (Out::Data(d), Some(Out::Data(prev))) = (&o, out.last_mut()) {
            prev.extend_from_slice(d);
            return;
        }
        out.push(o);
    };
    for (i, piece) in pieces.iter().enumerate() {
        let fin = i + 1 == pieces.len();
        let mut input: &[u8] = piece;
        loop {
            let (e, used) = r.next(input, fin);
            assert!(used <= input.len());
            let o = match e {
                Event::Need => {
                    assert_eq!(used, input.len());
                    None
                }
                Event::End => Some(Out::End),
                Event::Error(c) => Some(Out::Error(c)),
                Event::Handoff => Some(Out::Handoff),
                Event::StreamType(t) => Some(Out::Type(t)),
                Event::PushId(t) => Some(Out::PushId(t)),
                Event::Data(a, b) => Some(Out::Data(input[a..b].to_vec())),
                Event::Headers(s) => Some(Out::Headers(src(&r, input, s))),
                Event::PushPromise(id, s) => Some(Out::PushPromise(id, src(&r, input, s))),
                Event::Settings(s) => Some(Out::Settings(s)),
                Event::CancelPush(v) => Some(Out::CancelPush(v)),
                Event::Goaway(v) => Some(Out::Goaway(v)),
                Event::MaxPushId(v) => Some(Out::MaxPushId(v)),
            };
            input = &input[used..];
            match o {
                None => break,
                Some(o @ (Out::End | Out::Error(_) | Out::Handoff)) => {
                    push(o, &mut out);
                    return out;
                }
                Some(o) => push(o, &mut out),
            }
        }
    }
    out
}

/// The same events whole, and split at every pair of points.
fn check(mk: impl Fn() -> Reader, s: &[u8], want: &[Out]) {
    assert_eq!(feed(mk(), &[s]), want, "whole");
    for i in 0..=s.len() {
        assert_eq!(feed(mk(), &[&s[..i], &s[i..]]), want, "split at {i}");
        for j in i..=s.len() {
            assert_eq!(feed(mk(), &[&s[..i], &s[i..j], &s[j..]]), want, "split at {i}, {j}");
        }
    }
    // One byte at a time.
    let bytes: Vec<&[u8]> = s.chunks(1).collect();
    if !bytes.is_empty() {
        assert_eq!(feed(mk(), &bytes), want, "bytewise");
    }
}

const LIM: u64 = 1 << 16;

#[test]
fn request() {
    let mut s = frame(HEADERS, b"hdrs");
    s.extend(frame(0x21, b"grease"));
    s.extend(frame(DATA, b"hello "));
    s.extend(frame(DATA, b""));
    s.extend(frame(DATA, b"world"));
    s.extend(frame(HEADERS, b"trl"));
    check(
        || Reader::new_request(true, LIM),
        &s,
        &[Out::Headers(b"hdrs".to_vec()), Out::Data(b"hello world".to_vec()), Out::Headers(b"trl".to_vec()), Out::End],
    );
}

#[test]
fn request_errors() {
    let srv = || Reader::new_request(true, LIM);
    // DATA first.
    check(srv, &frame(DATA, b"x"), &[Out::Error(H3_FRAME_UNEXPECTED)]);
    // After trailers.
    let mut s = frame(HEADERS, b"h");
    s.extend(frame(HEADERS, b"t"));
    s.extend(frame(DATA, b"x"));
    check(srv, &s, &[Out::Headers(b"h".to_vec()), Out::Headers(b"t".to_vec()), Out::Error(H3_FRAME_UNEXPECTED)]);
    // Control frames, HTTP/2 frames, PUSH_PROMISE from a client.
    for t in [SETTINGS, GOAWAY, MAX_PUSH_ID, CANCEL_PUSH, 0x02, 0x06, 0x08, 0x09, PUSH_PROMISE] {
        let mut s = frame(HEADERS, b"h");
        s.extend(frame(t, &[0]));
        check(srv, &s, &[Out::Headers(b"h".to_vec()), Out::Error(H3_FRAME_UNEXPECTED)]);
    }
    // Ends before HEADERS; mid-frame.
    check(srv, &[], &[Out::Error(H3_REQUEST_INCOMPLETE)]);
    let s = frame(HEADERS, b"hdrs");
    check(srv, &s[..4], &[Out::Error(H3_FRAME_ERROR)]);
    // HEADERS beyond the limit.
    check(|| Reader::new_request(true, 3), &frame(HEADERS, b"hdrs"), &[Out::Error(H3_EXCESSIVE_LOAD)]);
}

#[test]
fn response() {
    let cli = || Reader::new_request(false, LIM);
    let mut s = frame(HEADERS, b"103");
    s.extend(frame(PUSH_PROMISE, &[&var(7)[..], b"pp"].concat()));
    s.extend(frame(HEADERS, b"200"));
    s.extend(frame(DATA, b"body"));
    s.extend(frame(PUSH_PROMISE, &[&var(300)[..], b"q"].concat()));
    check(
        cli,
        &s,
        &[
            Out::Headers(b"103".to_vec()),
            Out::PushPromise(7, b"pp".to_vec()),
            Out::Headers(b"200".to_vec()),
            Out::Data(b"body".to_vec()),
            Out::PushPromise(300, b"q".to_vec()),
            Out::End,
        ],
    );
    // An empty PUSH_PROMISE has no push ID.
    check(cli, &frame(PUSH_PROMISE, b""), &[Out::Error(H3_FRAME_ERROR)]);
    check(cli, &[], &[Out::Error(H3_MESSAGE_ERROR)]);
}

#[test]
fn control() {
    let srv = || Reader::new_uni(true, LIM);
    let mut s = var(STREAM_CONTROL);
    let mut set = Vec::new();
    for (id, v) in [(0x01u64, 4096u64), (0x21, 5), (0x06, 1 << 20), (0x07, 100), (0x08, 1), (0x33, 1), (0x40, 9)] {
        set.extend(var(id));
        set.extend(var(v));
    }
    s.extend(frame(SETTINGS, &set));
    s.extend(frame(0x21, b""));
    s.extend(frame(MAX_PUSH_ID, &var(10)));
    s.extend(frame(CANCEL_PUSH, &var(3)));
    s.extend(frame(GOAWAY, &var(1000)));
    s.extend(frame(MAX_PUSH_ID, &var(10)));
    s.extend(frame(GOAWAY, &var(999)));
    let want = Settings {
        qpack_max_table_capacity: Some(4096),
        max_field_section_size: Some(1 << 20),
        qpack_blocked_streams: Some(100),
        enable_connect_protocol: Some(1),
        h3_datagram: Some(1),
    };
    let mut ev = vec![
        Out::Type(0),
        Out::Settings(want),
        Out::MaxPushId(10),
        Out::CancelPush(3),
        Out::Goaway(1000),
        Out::MaxPushId(10),
        Out::Goaway(999),
    ];
    ev.push(Out::Error(H3_CLOSED_CRITICAL_STREAM));
    check(srv, &s, &ev);
}

#[test]
fn control_errors() {
    let srv = || Reader::new_uni(true, LIM);
    let cli = || Reader::new_uni(false, LIM);
    let ctl = |frames: &[Vec<u8>]| {
        let mut s = var(0);
        for f in frames {
            s.extend_from_slice(f);
        }
        s
    };
    let settings = frame(SETTINGS, &[]);
    let t = Out::Type(0);
    let st = Out::Settings(Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: None,
        qpack_blocked_streams: None,
        enable_connect_protocol: None,
        h3_datagram: None,
    });
    // SETTINGS must come first, even before unknown frames.
    check(srv, &ctl(&[frame(0x21, b"")]), &[t.clone(), Out::Error(H3_MISSING_SETTINGS)]);
    check(srv, &ctl(&[frame(GOAWAY, &var(0))]), &[t.clone(), Out::Error(H3_MISSING_SETTINGS)]);
    // A second SETTINGS; message frames.
    for f in [frame(SETTINGS, &[]), frame(DATA, b""), frame(HEADERS, b""), frame(PUSH_PROMISE, &var(0)), frame(0x06, b"")] {
        check(srv, &ctl(&[settings.clone(), f]), &[t.clone(), st.clone(), Out::Error(H3_FRAME_UNEXPECTED)]);
    }
    // SETTINGS payloads: HTTP/2 identifiers, repeats, bad booleans, truncation.
    for p in [
        [var(0x02), var(0)].concat(),
        [var(0x00), var(0)].concat(),
        [var(0x06), var(1), var(0x06), var(2)].concat(),
        [var(0x08), var(2)].concat(),
        [var(0x33), var(7)].concat(),
    ] {
        check(srv, &ctl(&[frame(SETTINGS, &p)]), &[t.clone(), Out::Error(H3_SETTINGS_ERROR)]);
    }
    for p in [var(0x06), [var(0x06), vec![0x40]].concat()] {
        check(srv, &ctl(&[frame(SETTINGS, &p)]), &[t.clone(), Out::Error(H3_FRAME_ERROR)]);
    }
    // Repeated unknown settings are ignored.
    check(
        srv,
        &ctl(&[frame(SETTINGS, &[var(0x21), var(1), var(0x21), var(2)].concat())]),
        &[t.clone(), st.clone(), Out::Error(H3_CLOSED_CRITICAL_STREAM)],
    );
    // One-varint payloads with bytes over, or too long to read.
    let two = [var(5), var(6)].concat();
    check(srv, &ctl(&[settings.clone(), frame(GOAWAY, &two)]), &[t.clone(), st.clone(), Out::Error(H3_FRAME_ERROR)]);
    check(srv, &ctl(&[settings.clone(), frame(GOAWAY, &[0; 9])]), &[t.clone(), st.clone(), Out::Error(H3_FRAME_ERROR)]);
    check(srv, &ctl(&[settings.clone(), frame(GOAWAY, &[])]), &[t.clone(), st.clone(), Out::Error(H3_FRAME_ERROR)]);
    // IDs.
    check(srv, &ctl(&[settings.clone(), frame(CANCEL_PUSH, &var(0))]), &[t.clone(), st.clone(), Out::Error(H3_ID_ERROR)]);
    check(
        srv,
        &ctl(&[settings.clone(), frame(MAX_PUSH_ID, &var(5)), frame(MAX_PUSH_ID, &var(4))]),
        &[t.clone(), st.clone(), Out::MaxPushId(5), Out::Error(H3_ID_ERROR)],
    );
    check(
        srv,
        &ctl(&[settings.clone(), frame(GOAWAY, &var(5)), frame(GOAWAY, &var(6))]),
        &[t.clone(), st.clone(), Out::Goaway(5), Out::Error(H3_ID_ERROR)],
    );
    check(cli, &ctl(&[settings.clone(), frame(GOAWAY, &var(5))]), &[t.clone(), st.clone(), Out::Error(H3_ID_ERROR)]);
    check(cli, &ctl(&[settings.clone(), frame(MAX_PUSH_ID, &var(5))]), &[t.clone(), st.clone(), Out::Error(H3_FRAME_UNEXPECTED)]);
    check(cli, &ctl(&[settings.clone(), frame(CANCEL_PUSH, &var(5))]), &[t.clone(), st.clone(), Out::CancelPush(5), Out::Error(H3_CLOSED_CRITICAL_STREAM)]);
}

#[test]
fn uni_types() {
    // Push streams: only to clients.
    let mut s = var(STREAM_PUSH);
    s.extend(var(12345));
    s.extend(frame(HEADERS, b"200"));
    s.extend(frame(DATA, b"pushed"));
    check(
        || Reader::new_uni(false, LIM),
        &s,
        &[Out::Type(1), Out::PushId(12345), Out::Headers(b"200".to_vec()), Out::Data(b"pushed".to_vec()), Out::End],
    );
    check(|| Reader::new_uni(true, LIM), &s, &[Out::Error(H3_STREAM_CREATION_ERROR)]);
    let mut p = var(STREAM_PUSH);
    p.extend(var(1));
    p.extend(frame(PUSH_PROMISE, &var(0)));
    check(|| Reader::new_uni(false, LIM), &p, &[Out::Type(1), Out::PushId(1), Out::Error(H3_FRAME_UNEXPECTED)]);
    // QPACK and unknown types are handed off.
    for t in [2u64, 3, 0x21, 1 << 40] {
        let mut s = var(t);
        s.extend_from_slice(b"rest");
        assert_eq!(feed(Reader::new_uni(true, LIM), &[&s]), vec![Out::Type(t), Out::Handoff]);
    }
    // A stream may end before its type.
    check(|| Reader::new_uni(true, LIM), &[], &[Out::End]);
    check(|| Reader::new_uni(true, LIM), &[0x40], &[Out::End]);
}

#[test]
fn large_data_is_streamed() {
    let body = vec![7u8; 1 << 20];
    let mut s = frame(HEADERS, b"h");
    s.extend(frame(DATA, &body));
    // Limit 16 bytes: DATA is not buffered, so it is not limited.
    let mut r = Reader::new_request(true, 16);
    let mut input: &[u8] = &s;
    let mut got = 0;
    loop {
        let (e, used) = r.next(input, true);
        match e {
            Event::Data(a, b) => got += b - a,
            Event::End => break,
            Event::Headers(_) => {}
            e => panic!("{e:?}"),
        }
        input = &input[used..];
    }
    assert_eq!(got, body.len());
    assert!(r.buffered().len() < 16);
}
