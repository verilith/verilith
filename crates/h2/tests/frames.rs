//! Frames by hand from RFC 9113's layouts, every error rule of §4 and §6,
//! and generated frames: round trips, every short prefix, and random bytes.
use verilith_h2::spec::*;
use verilith_h2::{encode_head, parse, serialize, serialize_settings, Frame, Params, Parsed, Priority, Setting};

const MAX: u32 = 16384;

fn head(len: u32, ty: u8, flags: u8, stream: u32) -> Vec<u8> {
    encode_head(len, ty, flags, stream).unwrap().to_vec()
}

fn frame(ty: u8, flags: u8, stream: u32, payload: &[u8]) -> Vec<u8> {
    let mut v = head(payload.len() as u32, ty, flags, stream);
    v.extend_from_slice(payload);
    v
}

fn ser(f: &Frame) -> Vec<u8> {
    let mut v = Vec::new();
    serialize(f, MAX, &mut v).expect("well-formed");
    v
}

#[test]
fn head_layout() {
    // §4.1: length 24 bits, type, flags, R + 31-bit stream identifier.
    assert_eq!(head(0x010203, 0x7, 0x5a, 0x0405_0607), [1, 2, 3, 7, 0x5a, 4, 5, 6, 7]);
    assert_eq!(encode_head(1 << 24, 0, 0, 1), None);
    assert_eq!(encode_head(0, 0, 0, 1 << 31), None);
}

#[test]
fn data() {
    let b = frame(DATA, FLAG_END_STREAM, 1, b"hello");
    let f = Frame::Data { stream: 1, end_stream: true, pad: None, data: b"hello" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 14));
    assert_eq!(ser(&f), b);
    // Padded: Pad Length 3, then the data, then 3 bytes of padding.
    let b = frame(DATA, FLAG_PADDED, 3, b"\x03abc\0\0\0");
    let f = Frame::Data { stream: 3, end_stream: false, pad: Some(3), data: b"abc" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, b.len()));
    assert_eq!(ser(&f), b);
    // Nonzero padding is accepted (§6.1: a receiver is not obliged to check).
    let b = frame(DATA, FLAG_PADDED, 3, b"\x02a\x01\x01");
    assert_eq!(parse(&b, MAX), Parsed::Frame(Frame::Data { stream: 3, end_stream: false, pad: Some(2), data: b"a" }, b.len()));
    // Padding that leaves no data is fine; padding longer than that is not.
    assert!(matches!(parse(&frame(DATA, FLAG_PADDED, 3, b"\x02\0\0"), MAX), Parsed::Frame(..)));
    assert_eq!(parse(&frame(DATA, FLAG_PADDED, 3, b"\x03\0\0"), MAX), Parsed::ConnError(PROTOCOL_ERROR));
    assert_eq!(parse(&frame(DATA, FLAG_PADDED, 3, b""), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(DATA, 0, 0, b"x"), MAX), Parsed::ConnError(PROTOCOL_ERROR));
    // Undefined flags and the reserved bit are ignored.
    let mut b = frame(DATA, 0xf6, 5, b"x");
    b[5] |= 0x80;
    assert_eq!(parse(&b, MAX), Parsed::Frame(Frame::Data { stream: 5, end_stream: false, pad: None, data: b"x" }, 10));
}

#[test]
fn headers() {
    let b = frame(HEADERS, FLAG_END_HEADERS | FLAG_END_STREAM, 1, b"\x82\x86");
    let f = Frame::Headers { stream: 1, end_stream: true, end_headers: true, pad: None, priority: None, fragment: b"\x82\x86" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, b.len()));
    assert_eq!(ser(&f), b);
    // PADDED and PRIORITY: Pad Length, E + dependency, weight, fragment, padding.
    let b = frame(HEADERS, FLAG_PADDED | FLAG_PRIORITY, 7, b"\x01\x80\0\0\x03\x0f\x82\0");
    let pr = Priority { exclusive: true, dependency: 3, weight: 15 };
    let f = Frame::Headers { stream: 7, end_stream: false, end_headers: false, pad: Some(1), priority: Some(pr), fragment: b"\x82" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, b.len()));
    assert_eq!(ser(&f), b);
    assert_eq!(parse(&frame(HEADERS, FLAG_PRIORITY, 1, b"\0\0\0"), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(HEADERS, FLAG_PADDED | FLAG_PRIORITY, 1, b"\x01\0\0\0\0\0"), MAX), Parsed::ConnError(PROTOCOL_ERROR));
    assert_eq!(parse(&frame(HEADERS, 0, 0, b""), MAX), Parsed::ConnError(PROTOCOL_ERROR));
}

#[test]
fn priority_rst_settings() {
    let b = frame(PRIORITY, 0, 3, b"\0\0\0\x01\x10");
    let f = Frame::Priority { stream: 3, prio: Priority { exclusive: false, dependency: 1, weight: 16 } };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 14));
    assert_eq!(ser(&f), b);
    // §6.3: a PRIORITY frame of the wrong length is a stream error.
    assert_eq!(parse(&frame(PRIORITY, 0, 3, b"\0\0\0\x01"), MAX), Parsed::StreamError { stream: 3, code: FRAME_SIZE_ERROR, len: 13 });
    assert_eq!(parse(&frame(PRIORITY, 0, 0, b"\0\0\0\x01\x10"), MAX), Parsed::ConnError(PROTOCOL_ERROR));

    let b = frame(RST_STREAM, 0, 9, b"\0\0\0\x08");
    let f = Frame::RstStream { stream: 9, code: CANCEL };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 13));
    assert_eq!(ser(&f), b);
    assert_eq!(parse(&frame(RST_STREAM, 0, 9, b"\0\0\x08"), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(RST_STREAM, 0, 0, b"\0\0\0\x08"), MAX), Parsed::ConnError(PROTOCOL_ERROR));

    let p = b"\0\x03\0\0\0\x64\0\x04\0\0\xff\xff\x12\x34\0\0\0\x07";
    let b = frame(SETTINGS, 0, 0, p);
    let Parsed::Frame(Frame::Settings { ack: false, params }, 27) = parse(&b, MAX) else { panic!() };
    assert_eq!(params.len(), 3);
    assert_eq!(params.get(0), Setting { id: SETTINGS_MAX_CONCURRENT_STREAMS, value: 100 });
    assert_eq!(params.get(1), Setting { id: SETTINGS_INITIAL_WINDOW_SIZE, value: 65535 });
    assert_eq!(params.get(2), Setting { id: 0x1234, value: 7 }); // unknown, kept
    assert_eq!(ser(&Frame::Settings { ack: false, params }), b);
    let mut v = Vec::new();
    serialize_settings(&[params.get(0), params.get(1), params.get(2)], MAX, &mut v).unwrap();
    assert_eq!(v, b);
    assert_eq!(parse(&frame(SETTINGS, FLAG_ACK, 0, b""), MAX), Parsed::Frame(Frame::Settings { ack: true, params: Params::new(b"").unwrap() }, 9));
    assert_eq!(parse(&frame(SETTINGS, FLAG_ACK, 0, &p[..6]), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(SETTINGS, 0, 0, &p[..5]), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(SETTINGS, 0, 1, &p[..6]), MAX), Parsed::ConnError(PROTOCOL_ERROR));
    for (id, value, code) in [
        (SETTINGS_ENABLE_PUSH, 2, Some(PROTOCOL_ERROR)),
        (SETTINGS_ENABLE_PUSH, 1, None),
        (SETTINGS_INITIAL_WINDOW_SIZE, 0x8000_0000, Some(FLOW_CONTROL_ERROR)),
        (SETTINGS_INITIAL_WINDOW_SIZE, 0x7fff_ffff, None),
        (SETTINGS_MAX_FRAME_SIZE, 16383, Some(PROTOCOL_ERROR)),
        (SETTINGS_MAX_FRAME_SIZE, 16384, None),
        (SETTINGS_MAX_FRAME_SIZE, 16777215, None),
        (SETTINGS_MAX_FRAME_SIZE, 16777216, Some(PROTOCOL_ERROR)),
        (SETTINGS_ENABLE_CONNECT_PROTOCOL, 2, Some(PROTOCOL_ERROR)),
        (SETTINGS_NO_RFC7540_PRIORITIES, 2, Some(PROTOCOL_ERROR)),
        (SETTINGS_HEADER_TABLE_SIZE, u32::MAX, None),
    ] {
        let mut q = vec![0, 3, 0, 0, 0, 1];
        q.extend_from_slice(&id.to_be_bytes());
        q.extend_from_slice(&value.to_be_bytes());
        let fb = frame(SETTINGS, 0, 0, &q);
        let r = parse(&fb, MAX);
        match code {
            Some(c) => {
                assert_eq!(r, Parsed::ConnError(c), "{id} {value}");
                let s = [Setting { id, value }];
                assert_eq!(serialize_settings(&s, MAX, &mut Vec::new()), Err(()));
            }
            None => assert!(matches!(r, Parsed::Frame(..)), "{id} {value}"),
        }
    }
}

#[test]
fn push_ping_goaway_window_continuation() {
    let b = frame(PUSH_PROMISE, FLAG_END_HEADERS, 1, b"\0\0\0\x02\x82");
    let f = Frame::PushPromise { stream: 1, end_headers: true, pad: None, promised: 2, fragment: b"\x82" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, b.len()));
    assert_eq!(ser(&f), b);
    assert_eq!(parse(&frame(PUSH_PROMISE, 0, 1, b"\0\0\0"), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(PUSH_PROMISE, FLAG_PADDED, 1, b"\x01\0\0\0\x02"), MAX), Parsed::ConnError(PROTOCOL_ERROR));

    let b = frame(PING, FLAG_ACK, 0, b"\x01\x02\x03\x04\x05\x06\x07\x08");
    let f = Frame::Ping { ack: true, opaque: 0x0102030405060708 };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 17));
    assert_eq!(ser(&f), b);
    assert_eq!(parse(&frame(PING, 0, 0, b"1234567"), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(PING, 0, 1, b"12345678"), MAX), Parsed::ConnError(PROTOCOL_ERROR));

    let b = frame(GOAWAY, 0, 0, b"\0\0\0\x05\0\0\0\x0bbye");
    let f = Frame::GoAway { last_stream: 5, code: ENHANCE_YOUR_CALM, debug: b"bye" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, b.len()));
    assert_eq!(ser(&f), b);
    assert_eq!(parse(&frame(GOAWAY, 0, 0, b"\0\0\0\x05\0\0\0"), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&frame(GOAWAY, 0, 3, b"\0\0\0\x05\0\0\0\0"), MAX), Parsed::ConnError(PROTOCOL_ERROR));

    let b = frame(WINDOW_UPDATE, 0, 0, b"\x7f\xff\xff\xff");
    let f = Frame::WindowUpdate { stream: 0, increment: MAX_31 };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 13));
    assert_eq!(ser(&f), b);
    // §6.9: an increment of 0 is a stream error, or a connection error on stream 0.
    assert_eq!(parse(&frame(WINDOW_UPDATE, 0, 5, b"\0\0\0\0"), MAX), Parsed::StreamError { stream: 5, code: PROTOCOL_ERROR, len: 13 });
    assert_eq!(parse(&frame(WINDOW_UPDATE, 0, 0, b"\x80\0\0\0"), MAX), Parsed::ConnError(PROTOCOL_ERROR));
    assert_eq!(parse(&frame(WINDOW_UPDATE, 0, 5, b"\0\0\0\0\0"), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(serialize(&Frame::WindowUpdate { stream: 1, increment: 0 }, MAX, &mut Vec::new()), Err(()));

    let b = frame(CONTINUATION, FLAG_END_HEADERS, 1, b"\x84");
    let f = Frame::Continuation { stream: 1, end_headers: true, fragment: b"\x84" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 10));
    assert_eq!(ser(&f), b);
    assert_eq!(parse(&frame(CONTINUATION, 0, 0, b""), MAX), Parsed::ConnError(PROTOCOL_ERROR));

    let b = frame(0xfa, 0x33, 0, b"ext");
    let f = Frame::Unknown { ty: 0xfa, flags: 0x33, stream: 0, payload: b"ext" };
    assert_eq!(parse(&b, MAX), Parsed::Frame(f, 12));
    assert_eq!(ser(&f), b);
}

#[test]
fn frame_size() {
    // §4.2: too long for SETTINGS_MAX_FRAME_SIZE is an error from the header alone.
    assert_eq!(parse(&head(MAX + 1, DATA, 0, 1), MAX), Parsed::ConnError(FRAME_SIZE_ERROR));
    assert_eq!(parse(&head(MAX, DATA, 0, 1), MAX), Parsed::Incomplete(9 + MAX as usize));
    assert_eq!(parse(&head(MAX + 1, DATA, 0, 1), MAX + 1), Parsed::Incomplete(10 + MAX as usize));
    assert_eq!(parse(&[0; 8], MAX), Parsed::Incomplete(9));
    let big = vec![0u8; MAX as usize + 1];
    let f = Frame::Data { stream: 1, end_stream: false, pad: None, data: &big };
    assert_eq!(serialize(&f, MAX, &mut Vec::new()), Err(()));
    let f = Frame::Data { stream: 1, end_stream: false, pad: Some(1), data: &big[..MAX as usize - 1] };
    assert_eq!(serialize(&f, MAX, &mut Vec::new()), Err(()));
    let f = Frame::Data { stream: 1, end_stream: false, pad: Some(0), data: &big[..MAX as usize - 1] };
    assert_eq!(ser(&f).len(), 9 + MAX as usize);
}

// ---------------------------------------------------------------------------
// Generated frames
// ---------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn bool(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

fn gen_frame<'a>(r: &mut Rng, buf: &'a [u8], params: &'a [u8]) -> Frame<'a> {
    let stream = 1 + r.below(MAX_31 as u64) as u32;
    let bytes = &buf[..r.below(200) as usize];
    let pad = if r.bool() { Some(r.below(256) as u8) } else { None };
    let prio = || Priority { exclusive: stream & 1 == 1, dependency: stream / 2, weight: stream as u8 };
    match r.below(11) {
        0 => Frame::Data { stream, end_stream: r.bool(), pad, data: bytes },
        1 => Frame::Headers { stream, end_stream: r.bool(), end_headers: r.bool(), pad, priority: if r.bool() { Some(prio()) } else { None }, fragment: bytes },
        2 => Frame::Priority { stream, prio: prio() },
        3 => Frame::RstStream { stream, code: r.next() as u32 },
        4 => Frame::Settings { ack: false, params: Params::new(params).unwrap() },
        5 => Frame::PushPromise { stream, end_headers: r.bool(), pad, promised: stream / 3, fragment: bytes },
        6 => Frame::Ping { ack: r.bool(), opaque: r.next() },
        7 => Frame::GoAway { last_stream: stream - 1, code: r.next() as u32, debug: bytes },
        8 => Frame::WindowUpdate { stream: stream - 1, increment: stream },
        9 => Frame::Continuation { stream, end_headers: r.bool(), fragment: bytes },
        _ => Frame::Unknown { ty: 10 + r.below(246) as u8, flags: r.next() as u8, stream: stream - 1, payload: bytes },
    }
}

#[test]
fn round_trip_generated() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    let buf: Vec<u8> = (0..256).map(|_| r.next() as u8).collect();
    let mut params = Vec::new();
    for i in 0..r.below(8) + 1 {
        params.extend_from_slice(&(10 + i as u16).to_be_bytes());
        params.extend_from_slice(&(r.next() as u32).to_be_bytes());
    }
    for _ in 0..20000 {
        let f = gen_frame(&mut r, &buf, &params);
        let mut b = ser(&f);
        let n = b.len();
        // Every short prefix is Incomplete, and asks for no more than the frame.
        for k in [0, 1, 8, 9, n / 2, n - 1] {
            if k < n {
                match parse(&b[..k], MAX) {
                    Parsed::Incomplete(need) => assert!(need > k && need <= n),
                    other => panic!("{f:?} prefix {k}: {other:?}"),
                }
            }
        }
        b.extend_from_slice(&buf[..r.below(20) as usize]);
        assert_eq!(parse(&b, MAX), Parsed::Frame(f, n), "{f:?}");
    }
}

#[test]
fn random_bytes() {
    let mut r = Rng(12345);
    let mut b = vec![0u8; 64];
    for _ in 0..200000 {
        for x in b.iter_mut() {
            *x = r.next() as u8;
        }
        let len = r.below(56) as u32;
        b[..3].copy_from_slice(&len.to_be_bytes()[1..]);
        b[3] = r.below(12) as u8;
        if r.bool() {
            b[5..9].copy_from_slice(&[0, 0, 0, 0]);
        }
        match parse(&b, MAX) {
            Parsed::Frame(f, n) => {
                assert_eq!(n, 9 + len as usize);
                // Re-sent, it reads back the same (lemma_parse_wf + lemma_roundtrip).
                let v = ser(&f);
                assert_eq!(v.len(), n);
                assert_eq!(parse(&v, MAX), Parsed::Frame(f, n));
            }
            Parsed::StreamError { len: l, .. } => assert_eq!(l, 9 + len as usize),
            Parsed::ConnError(c) => assert!(c == PROTOCOL_ERROR || c == FRAME_SIZE_ERROR || c == FLOW_CONTROL_ERROR),
            Parsed::Incomplete(_) => panic!(),
        }
    }
}
