//! The public writers through the reader: random streams of written
//! frames, fed in random pieces, come back as the frames written.
use verilith_h3::consts::*;
use verilith_h3::*;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
    /// A value of random encoded size, at most `max`.
    fn val(&mut self, max: u64) -> u64 {
        let bits = [6, 14, 30, 62][self.below(4) as usize];
        (self.next() & ((1u64 << bits) - 1)).min(max)
    }
    /// Up to `max` random bytes.
    fn bytes(&mut self, max: u64) -> Vec<u8> {
        let n = self.below(max + 1);
        (0..n).map(|_| self.next() as u8).collect()
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Out {
    Type(u64),
    Data(Vec<u8>),
    Headers(Vec<u8>),
    PushPromise(u64, Vec<u8>),
    Settings(Settings),
    CancelPush(u64),
    Goaway(u64),
    MaxPushId(u64),
    End,
    Error(u64),
}

fn grow(out: &mut Vec<u8>, n: usize) -> usize {
    let at = out.len();
    out.resize(at + n, 0);
    at
}

fn header(out: &mut Vec<u8>, t: u64, p: &[u8]) {
    let at = grow(out, 16);
    let e = write_header(out, at, t, p.len() as u64).unwrap();
    assert_eq!(e - at, header_size(t, p.len() as u64));
    out.truncate(e);
    out.extend_from_slice(p);
}

fn id_frame(out: &mut Vec<u8>, t: u64, v: u64) {
    let at = grow(out, 10);
    let e = write_id_frame(out, at, t, v).unwrap();
    out.truncate(e);
}

fn settings(out: &mut Vec<u8>, s: &Settings) {
    let n = settings_frame_size(s).unwrap();
    let at = grow(out, n);
    assert_eq!(write_settings(out, at, s), Some(at + n));
}

fn feed(mut r: Reader, s: &[u8], cuts: &[usize], fin: bool) -> Vec<Out> {
    let mut out: Vec<Out> = Vec::new();
    let mut at = 0;
    let mut ends: Vec<usize> = cuts.to_vec();
    ends.push(s.len());
    for (i, &end) in ends.iter().enumerate() {
        let last = i + 1 == ends.len();
        let mut input = &s[at..end];
        at = end;
        loop {
            let (e, used) = r.next(input, fin && last);
            assert!(used <= input.len());
            let o = match e {
                Event::Need => {
                    assert_eq!(used, input.len());
                    break;
                }
                Event::End => Out::End,
                Event::Error(c) => Out::Error(c),
                Event::StreamType(t) => Out::Type(t),
                Event::Data(a, b) => Out::Data(input[a..b].to_vec()),
                Event::Headers(src) => Out::Headers(take(&r, input, src)),
                Event::PushPromise(id, src) => Out::PushPromise(id, take(&r, input, src)),
                Event::Settings(s) => Out::Settings(s),
                Event::CancelPush(v) => Out::CancelPush(v),
                Event::Goaway(v) => Out::Goaway(v),
                Event::MaxPushId(v) => Out::MaxPushId(v),
                e => panic!("{e:?}"),
            };
            input = &input[used..];
            let stop = matches!(o, Out::End | Out::Error(_));
            match (o, out.last_mut()) {
                (Out::Data(d), Some(Out::Data(prev))) => prev.extend(d),
                (o, _) => out.push(o),
            }
            if stop {
                return out;
            }
        }
    }
    out
}

fn take(r: &Reader, input: &[u8], s: Src) -> Vec<u8> {
    match s {
        Src::Input(a, b) => input[a..b].to_vec(),
        Src::Buf(off) => r.buffered()[off..].to_vec(),
    }
}

fn cuts(rng: &mut Rng, len: usize) -> Vec<usize> {
    let mut c: Vec<usize> = (0..rng.below(6)).map(|_| rng.below(len as u64 + 1) as usize).collect();
    c.sort();
    c
}

const LIM: u64 = 1 << 16;

#[test]
fn request_streams() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for round in 0..3000 {
        let mut s = Vec::new();
        let mut want = Vec::new();
        let head = rng.bytes(200);
        header(&mut s, HEADERS, &head);
        want.push(Out::Headers(head));
        let mut body = Vec::new();
        for _ in 0..rng.below(6) {
            if rng.below(3) == 0 {
                // A reserved type (0x1f * N + 0x21), which the reader skips.
                let t = 0x1f * rng.below(1000) + 0x21;
                let p = rng.bytes(30);
                header(&mut s, t, &p);
            } else {
                let d = rng.bytes(3000);
                header(&mut s, DATA, &d);
                body.extend(d);
            }
        }
        if !body.is_empty() {
            want.push(Out::Data(body));
        }
        if rng.below(2) == 0 {
            let tr = { let mut t = rng.bytes(50); t.push(1); t };
            header(&mut s, HEADERS, &tr);
            want.push(Out::Headers(tr));
        }
        want.push(Out::End);
        let c = cuts(&mut rng, s.len());
        assert_eq!(feed(Reader::new_request(true, LIM), &s, &c, true), want, "round {round}, cuts {c:?}");
    }
}

#[test]
fn control_streams() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let opt = |rng: &mut Rng, max: u64| if rng.below(2) == 0 { None } else { Some(rng.val(max)) };
    for round in 0..3000 {
        let mut s = Vec::new();
        let at = grow(&mut s, 8);
        let e = write_var(&mut s, at, STREAM_CONTROL).unwrap();
        s.truncate(e);
        let set = Settings {
            qpack_max_table_capacity: opt(&mut rng, MAX_VARINT),
            max_field_section_size: opt(&mut rng, MAX_VARINT),
            qpack_blocked_streams: opt(&mut rng, MAX_VARINT),
            enable_connect_protocol: opt(&mut rng, 1),
            h3_datagram: opt(&mut rng, 1),
        };
        settings(&mut s, &set);
        let mut want = vec![Out::Type(STREAM_CONTROL), Out::Settings(set)];
        // At a server: GOAWAY push IDs never increase, MAX_PUSH_ID never
        // decreases.
        let mut goaway = MAX_VARINT;
        // CANCEL_PUSH names a push ID up to the MAX_PUSH_ID received.
        let mut max_push: Option<u64> = None;
        for _ in 0..rng.below(8) {
            match rng.below(3) {
                0 => {
                    goaway = rng.val(goaway);
                    id_frame(&mut s, GOAWAY, goaway);
                    want.push(Out::Goaway(goaway));
                }
                1 => {
                    let m = (max_push.unwrap_or(0) + rng.val(1000)).min(MAX_VARINT);
                    max_push = Some(m);
                    id_frame(&mut s, MAX_PUSH_ID, m);
                    want.push(Out::MaxPushId(m));
                }
                _ => {
                    let Some(m) = max_push else { continue };
                    let v = rng.val(m);
                    id_frame(&mut s, CANCEL_PUSH, v);
                    want.push(Out::CancelPush(v));
                }
            }
        }
        let c = cuts(&mut rng, s.len());
        assert_eq!(feed(Reader::new_uni(true, LIM), &s, &c, false), want, "round {round}, cuts {c:?}");
        // A control stream may not end.
        want.push(Out::Error(H3_CLOSED_CRITICAL_STREAM));
        assert_eq!(feed(Reader::new_uni(true, LIM), &s, &c, true), want, "round {round}, cuts {c:?}");
    }
}

#[test]
fn push_streams() {
    let mut rng = Rng(7);
    for _ in 0..2000 {
        // A response with a PUSH_PROMISE, at a client.
        let mut s = Vec::new();
        let id = rng.val(MAX_VARINT);
        let sec = rng.bytes(100);
        let at = grow(&mut s, 20);
        let e = write_push_promise_head(&mut s, at, id, sec.len() as u64).unwrap();
        s.truncate(e);
        s.extend_from_slice(&sec);
        let head = rng.bytes(100);
        header(&mut s, HEADERS, &head);
        let c = cuts(&mut rng, s.len());
        let want = vec![Out::PushPromise(id, sec), Out::Headers(head), Out::End];
        assert_eq!(feed(Reader::new_request(false, LIM), &s, &c, true), want);
    }
}

#[test]
fn writers_check() {
    let mut b = [0u8; 4];
    assert_eq!(write_var(&mut b, 0, 1 << 62), None);
    assert_eq!(write_var(&mut b, 1, 1 << 20), None);
    assert_eq!(write_var(&mut b, 0, 1 << 20), Some(4));
    assert_eq!(write_var(&mut b, 9, 0), None);
    assert_eq!(write_header(&mut b, 3, DATA, 0), None);
    assert_eq!(write_header(&mut b, 2, DATA, 0), Some(4));
    assert_eq!(write_id_frame(&mut b, 0, DATA, 1), None);
    assert_eq!(write_id_frame(&mut b, 0, GOAWAY, 64), Some(4));
    assert_eq!(write_id_frame(&mut b, 1, GOAWAY, 64), None);
    assert_eq!(write_id_frame(&mut b, usize::MAX, GOAWAY, 0), None);
    assert_eq!(write_push_promise_head(&mut b, usize::MAX, 0, 0), None);
    let bad = Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: None,
        qpack_blocked_streams: None,
        enable_connect_protocol: Some(2),
        h3_datagram: None,
    };
    assert_eq!(settings_frame_size(&bad), None);
    assert_eq!(write_settings(&mut [0u8; 100], 0, &bad), None);
    let ok = Settings { enable_connect_protocol: Some(1), ..bad };
    assert_eq!(settings_frame_size(&ok), Some(4));
    assert_eq!(write_settings(&mut b, 1, &ok), None);
    assert_eq!(write_settings(&mut b, 0, &ok), Some(4));
    assert_eq!(b, [0x04, 0x02, 0x08, 0x01]);
}
