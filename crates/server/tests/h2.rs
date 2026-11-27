//! The HTTP/2 engine: requests in frames, split every way, responses read
//! back with verilith-h2's parser and verilith-hpack's decoder.
use verilith_h2::{serialize, Frame, Params, Parsed};
use verilith_hpack::{Decoder, Feed};
use verilith_server::h1::Ctx;
use verilith_server::h2::{Conn2, PREFACE};
use verilith_server::{Field, Limits2, Request, Response};

fn handler(req: &Request, res: &mut Response) {
    let mut body = Vec::new();
    body.extend_from_slice(req.method);
    body.push(b' ');
    body.extend_from_slice(req.target);
    body.push(b' ');
    body.extend_from_slice(req.body);
    if req.target == b"/big" {
        body.resize(100_000, b'x');
    }
    let _ = res.send(200, &[Field { name: b"X-Test", value: b"1" }], &body);
}

/// A header block: `:method`, `:scheme`, `:path` as literals without
/// indexing with indexed names (RFC 7541 §6.2.2).
fn block(method: &[u8], path: &[u8]) -> Vec<u8> {
    let mut b = Vec::new();
    for (idx, v) in [(2u8, method), (6, &b"http"[..]), (4, path)] {
        b.push(idx);
        b.push(v.len() as u8);
        b.extend_from_slice(v);
    }
    b
}

fn client_stream() -> Vec<u8> {
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
    let b1 = block(b"GET", b"/a");
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b1 }, 16384, &mut c).unwrap();
    // A POST whose block is split across HEADERS and CONTINUATION, then DATA.
    let b3 = block(b"POST", b"/b");
    let (x, y) = b3.split_at(5);
    serialize(&Frame::Headers { stream: 3, end_stream: false, end_headers: false, pad: None, priority: None, fragment: x }, 16384, &mut c).unwrap();
    serialize(&Frame::Continuation { stream: 3, end_headers: true, fragment: y }, 16384, &mut c).unwrap();
    serialize(&Frame::Data { stream: 3, end_stream: false, pad: None, data: b"hel" }, 16384, &mut c).unwrap();
    serialize(&Frame::Ping { ack: false, opaque: 7 }, 16384, &mut c).unwrap();
    serialize(&Frame::Data { stream: 3, end_stream: true, pad: Some(3), data: b"lo" }, 16384, &mut c).unwrap();
    c
}

/// Runs the engine over `input` cut at `cuts`, and returns what it wrote.
fn run(input: &[u8], cuts: &[usize]) -> Vec<u8> {
    let mut c = Conn2::new(Limits2::default());
    let ctx = Ctx::new(b"t", b"Thu, 01 Jan 1970 00:00:00 GMT").unwrap();
    let mut out = Vec::new();
    let mut at = 0;
    for &cut in cuts.iter().chain(std::iter::once(&input.len())) {
        let mut p = &input[at..cut];
        at = cut;
        while !p.is_empty() {
            let b = c.read_buf();
            if b.is_empty() {
                // Closing: the engine takes no more input.
                return out;
            }
            let n = b.len().min(p.len());
            b[..n].copy_from_slice(&p[..n]);
            c.filled(n);
            p = &p[n..];
            c.process(&handler, &ctx);
            drain(&mut c, &mut out);
        }
    }
    out
}

fn drain(c: &mut Conn2, out: &mut Vec<u8>) {
    loop {
        let mut v: [&[u8]; 8] = [&[]; 8];
        let k = c.pending(&mut v);
        if k == 0 {
            break;
        }
        let mut n = 0;
        for s in &v[..k] {
            out.extend_from_slice(s);
            n += s.len();
        }
        c.wrote(n);
    }
}

/// (stream, status, body) for each response, and the control frames seen.
fn responses(out: &[u8]) -> (Vec<(u32, Vec<(Vec<u8>, Vec<u8>)>, Vec<u8>)>, Vec<String>) {
    responses_with(out, None)
}

/// `responses`, with the client's decoder table limited to `table` bytes
/// (what its SETTINGS_HEADER_TABLE_SIZE said).
fn responses_with(out: &[u8], table: Option<u32>) -> (Vec<(u32, Vec<(Vec<u8>, Vec<u8>)>, Vec<u8>)>, Vec<String>) {
    let mut dec = Decoder::new().unwrap();
    if let Some(n) = table {
        assert!(dec.change_settings(n));
    }
    let mut rs: Vec<(u32, Vec<(Vec<u8>, Vec<u8>)>, Vec<u8>)> = Vec::new();
    let mut ctl = Vec::new();
    let mut rest = out;
    while !rest.is_empty() {
        match verilith_h2::parse(rest, 1 << 20) {
            Parsed::Frame(f, n) => {
                match f {
                    Frame::Headers { stream, fragment, end_headers, .. } => {
                        assert!(end_headers);
                        let mut fields = Vec::new();
                        let mut fr = fragment;
                        loop {
                            match dec.feed(fr, true) {
                                Feed::Field(k, _) => {
                                    fields.push((dec.name().to_vec(), dec.value().to_vec()));
                                    fr = &fr[k..];
                                }
                                Feed::Final => break,
                                Feed::More => break,
                                Feed::Bad => panic!("bad HPACK from the server"),
                            }
                        }
                        dec.end_block();
                        rs.push((stream, fields, Vec::new()));
                    }
                    Frame::Data { stream, data, .. } => {
                        rs.iter_mut().find(|r| r.0 == stream).unwrap().2.extend_from_slice(data);
                    }
                    Frame::Settings { ack, .. } => ctl.push(format!("settings ack={ack}")),
                    Frame::Ping { ack, opaque } => ctl.push(format!("ping ack={ack} {opaque}")),
                    Frame::WindowUpdate { stream, .. } => ctl.push(format!("window {stream}")),
                    Frame::GoAway { code, .. } => ctl.push(format!("goaway {code}")),
                    Frame::RstStream { stream, code } => ctl.push(format!("rst {stream} {code}")),
                    other => panic!("unexpected {other:?}"),
                }
                rest = &rest[n..];
            }
            other => panic!("server wrote a bad frame: {other:?}"),
        }
    }
    (rs, ctl)
}

#[test]
fn requests_and_responses() {
    let out = run(&client_stream(), &[]);
    let (rs, ctl) = responses(&out);
    assert_eq!(rs.len(), 2);
    assert_eq!(rs[0].0, 1);
    assert_eq!(rs[0].1[0], (b":status".to_vec(), b"200".to_vec()));
    assert!(rs[0].1.contains(&(b"x-test".to_vec(), b"1".to_vec())));
    assert_eq!(rs[0].2, b"GET /a ");
    assert_eq!(rs[1].2, b"POST /b hello");
    assert!(ctl.contains(&"ping ack=true 7".to_string()));
    assert!(ctl.contains(&"settings ack=true".to_string()));
}

#[test]
fn split_anywhere_same_responses() {
    let input = client_stream();
    let whole = responses(&run(&input, &[])).0;
    for i in 0..=input.len() {
        assert_eq!(responses(&run(&input, &[i])).0, whole, "split at {i}");
    }
    let ones: Vec<usize> = (1..input.len()).collect();
    assert_eq!(responses(&run(&input, &ones)).0, whole);
}

#[test]
fn flow_control_holds_data_until_window_update() {
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
    let b = block(b"GET", b"/big");
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let out = run(&c, &[]);
    let (rs, _) = responses(&out);
    // The default window is 65535 bytes: no more DATA than that before an update.
    assert_eq!(rs[0].2.len(), 65535);
    let mut more = c.clone();
    serialize(&Frame::WindowUpdate { stream: 0, increment: 1 << 20 }, 16384, &mut more).unwrap();
    serialize(&Frame::WindowUpdate { stream: 1, increment: 1 << 20 }, 16384, &mut more).unwrap();
    let (rs, _) = responses(&run(&more, &[c.len()]));
    assert_eq!(rs[0].2.len(), 100_000);
}

#[test]
fn protocol_errors() {
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
    // An even stream ID from a client is a connection error.
    let b = block(b"GET", b"/a");
    serialize(&Frame::Headers { stream: 2, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let (_, ctl) = responses(&run(&c, &[]));
    assert!(ctl.contains(&"goaway 1".to_string()), "{ctl:?}");
    // A bad preface is too.
    let (_, ctl) = responses(&run(b"GET / HTTP/1.1\r\n\r\n", &[]));
    assert!(ctl.contains(&"goaway 1".to_string()), "{ctl:?}");
}

#[test]
fn ping_flood_is_stopped() {
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
    for i in 0..5000 {
        serialize(&Frame::Ping { ack: false, opaque: i }, 16384, &mut c).unwrap();
    }
    let (_, ctl) = responses(&run(&c, &[]));
    assert!(ctl.contains(&"goaway 11".to_string()));
    assert!(ctl.iter().filter(|s| s.starts_with("ping")).count() < 1100);
}

fn many_gets(n: u32, settings: &[u8]) -> Vec<u8> {
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(settings).unwrap() }, 16384, &mut c).unwrap();
    for i in 0..n {
        let b = block(b"GET", format!("/r{i}").as_bytes());
        serialize(&Frame::Headers { stream: 2 * i + 1, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    }
    c
}

/// Header block bytes the server wrote, per HEADERS frame.
fn block_sizes(out: &[u8]) -> Vec<usize> {
    let mut v = Vec::new();
    let mut rest = out;
    while let Parsed::Frame(f, n) = verilith_h2::parse(rest, 1 << 20) {
        if let Frame::Headers { fragment, .. } = f {
            v.push(fragment.len());
        }
        rest = &rest[n..];
    }
    v
}

#[test]
fn dynamic_table_shrinks_repeated_heads() {
    let input = many_gets(50, &[]);
    let out = run(&input, &[]);
    let (rs, _) = responses(&out);
    assert_eq!(rs.len(), 50);
    for (i, r) in rs.iter().enumerate() {
        assert_eq!(r.0, 2 * i as u32 + 1);
        assert_eq!(r.1[0], (b":status".to_vec(), b"200".to_vec()));
        assert!(r.1.contains(&(b"server".to_vec(), b"t".to_vec())));
        assert!(r.1.contains(&(b"x-test".to_vec(), b"1".to_vec())));
        assert_eq!(r.2, format!("GET /r{i} ").into_bytes());
    }
    let sizes = block_sizes(&out);
    // After the first head, the repeated fields are one-byte indices.
    assert!(sizes[10] * 3 < sizes[0], "{sizes:?}");
    // Split anywhere: the same responses (the table survives any cut).
    for i in (0..input.len()).step_by(7) {
        assert_eq!(responses(&run(&input, &[i])).0, rs, "split at {i}");
    }
}

#[test]
fn peer_table_size_zero_is_honoured() {
    let input = many_gets(5, &[0, 1, 0, 0, 0, 0]);
    let out = run(&input, &[]);
    let (rs, _) = responses_with(&out, Some(0));
    assert_eq!(rs.len(), 5);
    assert_eq!(rs[4].2, b"GET /r4 ");
}

#[test]
fn reset_before_headers_keeps_table_in_step() {
    // Stream 1 is answered but reset by the client in the same read,
    // before its HEADERS can go out; stream 3's head must still decode.
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
    let b = block(b"GET", b"/a");
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    serialize(&Frame::RstStream { stream: 1, code: 8 }, 16384, &mut c).unwrap();
    let b = block(b"GET", b"/b");
    serialize(&Frame::Headers { stream: 3, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let (rs, _) = responses(&run(&c, &[]));
    assert_eq!(rs.last().unwrap().2, b"GET /b ");
}

/// The stream-state table (streams.rs) as the engine applies it.
#[test]
fn stream_states() {
    let start = || {
        let mut c = PREFACE.to_vec();
        serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
        c
    };
    let get = |c: &mut Vec<u8>, id: u32| {
        let b = block(b"GET", b"/a");
        serialize(&Frame::Headers { stream: id, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, c).unwrap();
    };
    // DATA, RST_STREAM and WINDOW_UPDATE on an idle stream: PROTOCOL_ERROR.
    for f in [
        Frame::Data { stream: 5, end_stream: false, pad: None, data: b"x" },
        Frame::RstStream { stream: 5, code: 0 },
        Frame::WindowUpdate { stream: 5, increment: 1 },
        Frame::WindowUpdate { stream: 2, increment: 1 },
    ] {
        let mut c = start();
        serialize(&f, 16384, &mut c).unwrap();
        let (_, ctl) = responses(&run(&c, &[]));
        assert!(ctl.contains(&"goaway 1".to_string()), "{f:?}: {ctl:?}");
    }
    // A finished stream's ID again: STREAM_CLOSED; and a lower new ID too.
    for again in [1u32, 1] {
        let mut c = start();
        get(&mut c, 3);
        get(&mut c, again);
        let (rs, ctl) = responses(&run(&c, &[]));
        assert_eq!(rs.len(), 1);
        assert!(ctl.contains(&"goaway 5".to_string()), "{ctl:?}");
    }
    // WINDOW_UPDATE on a half-closed stream is fine; DATA there is a
    // stream error (the stream is reset, its response dropped), and the
    // connection goes on.
    let mut c = start();
    get(&mut c, 1);
    serialize(&Frame::WindowUpdate { stream: 1, increment: 10 }, 16384, &mut c).unwrap();
    serialize(&Frame::Data { stream: 1, end_stream: false, pad: None, data: b"x" }, 16384, &mut c).unwrap();
    get(&mut c, 3);
    let (rs, ctl) = responses(&run(&c, &[]));
    assert_eq!(rs.iter().map(|r| r.0).collect::<Vec<_>>(), vec![3], "{ctl:?}");
    assert!(ctl.contains(&"rst 1 5".to_string()), "{ctl:?}");
    assert!(!ctl.iter().any(|l| l.starts_with("goaway")), "{ctl:?}");
    // HEADERS without END_STREAM on an open stream (not trailers).
    let mut c = start();
    let b = block(b"POST", b"/a");
    serialize(&Frame::Headers { stream: 1, end_stream: false, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    serialize(&Frame::Headers { stream: 1, end_stream: false, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let (_, ctl) = responses(&run(&c, &[]));
    assert!(ctl.contains(&"goaway 1".to_string()), "{ctl:?}");
}

fn settings_frame() -> Vec<u8> {
    let mut c = PREFACE.to_vec();
    serialize(&Frame::Settings { ack: false, params: Params::new(&[]).unwrap() }, 16384, &mut c).unwrap();
    c
}

/// HEADERS (END_STREAM) then RST_STREAM, over and over: each reset costs
/// budget and no response completes, so the connection is closed long
/// before the handler has run for every request (CVE-2023-44487).
#[test]
fn rapid_reset_is_stopped() {
    let mut c = settings_frame();
    for i in 0..5000u32 {
        let b = block(b"GET", b"/a");
        let id = 2 * i + 1;
        serialize(&Frame::Headers { stream: id, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
        serialize(&Frame::RstStream { stream: id, code: 8 }, 16384, &mut c).unwrap();
    }
    let (rs, ctl) = responses(&run(&c, &[]));
    assert!(ctl.contains(&"goaway 11".to_string()), "{ctl:?}");
    assert!(rs.len() < 1100, "{}", rs.len());
}

/// Empty CONTINUATION frames never end a header block, and carry no
/// bytes for the block limit to count; each costs budget.
#[test]
fn empty_continuation_flood_is_stopped() {
    let mut c = settings_frame();
    let b = block(b"GET", b"/a");
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: false, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    for _ in 0..5000 {
        serialize(&Frame::Continuation { stream: 1, end_headers: false, fragment: &[] }, 16384, &mut c).unwrap();
    }
    let (_, ctl) = responses(&run(&c, &[]));
    assert!(ctl.contains(&"goaway 11".to_string()), "{ctl:?}");
}

/// A stream over SETTINGS_MAX_CONCURRENT_STREAMS is refused once its
/// block, CONTINUATION included, is decoded; the next request still works,
/// so the HPACK tables stayed in step.
#[test]
fn refused_stream_with_continuation() {
    let limits = Limits2 { max_streams: 1, ..Limits2::default() };
    let mut c = settings_frame();
    // Stream 1 stays open (no END_STREAM), so stream 3 is one too many.
    let b = block(b"POST", b"/a");
    serialize(&Frame::Headers { stream: 1, end_stream: false, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let b = block(b"GET", b"/b");
    let (x, y) = b.split_at(4);
    serialize(&Frame::Headers { stream: 3, end_stream: true, end_headers: false, pad: None, priority: None, fragment: x }, 16384, &mut c).unwrap();
    serialize(&Frame::Continuation { stream: 3, end_headers: true, fragment: y }, 16384, &mut c).unwrap();
    serialize(&Frame::Data { stream: 1, end_stream: true, pad: None, data: b"x" }, 16384, &mut c).unwrap();
    // In a later read, after stream 1's response has gone out.
    let cut = c.len();
    let b = block(b"GET", b"/c");
    serialize(&Frame::Headers { stream: 5, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let out = run_with(limits, &c, &[cut]);
    let (rs, ctl) = responses(&out);
    assert!(ctl.contains(&"rst 3 7".to_string()), "{ctl:?}");
    let bodies: Vec<_> = rs.iter().map(|r| (r.0, r.2.clone())).collect();
    assert_eq!(bodies, vec![(1, b"POST /a x".to_vec()), (5, b"GET /c ".to_vec())]);
}

/// A peer's GOAWAY(NO_ERROR) lets open streams finish (here, one blocked on
/// flow control until a WINDOW_UPDATE), refuses new ones, then closes.
#[test]
fn goaway_from_peer_drains() {
    let mut c = settings_frame();
    let b = block(b"GET", b"/big");
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    serialize(&Frame::GoAway { last_stream: 0, code: 0, debug: &[] }, 16384, &mut c).unwrap();
    let b = block(b"GET", b"/late");
    serialize(&Frame::Headers { stream: 3, end_stream: true, end_headers: true, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    let mid = c.len();
    serialize(&Frame::WindowUpdate { stream: 0, increment: 1 << 20 }, 16384, &mut c).unwrap();
    serialize(&Frame::WindowUpdate { stream: 1, increment: 1 << 20 }, 16384, &mut c).unwrap();
    let (rs, ctl) = responses(&run(&c, &[mid]));
    assert_eq!(rs.len(), 1);
    assert_eq!(rs[0].2.len(), 100_000);
    assert!(ctl.contains(&"rst 3 7".to_string()), "{ctl:?}");
    assert_eq!(ctl.last().map(|s| s.as_str()), Some("goaway 0"), "{ctl:?}");
}

/// Frames other than CONTINUATION inside a header block, and HEADERS
/// depending on its own stream, are connection errors.
#[test]
fn header_block_interleaving_is_an_error() {
    let mut c = settings_frame();
    let b = block(b"GET", b"/a");
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: false, pad: None, priority: None, fragment: &b }, 16384, &mut c).unwrap();
    serialize(&Frame::Ping { ack: false, opaque: 1 }, 16384, &mut c).unwrap();
    let (_, ctl) = responses(&run(&c, &[]));
    assert!(ctl.contains(&"goaway 1".to_string()), "{ctl:?}");
    assert!(!ctl.iter().any(|s| s.starts_with("ping")), "{ctl:?}");

    let mut c = settings_frame();
    let prio = verilith_h2::Priority { exclusive: false, dependency: 1, weight: 0 };
    serialize(&Frame::Headers { stream: 1, end_stream: true, end_headers: true, pad: None, priority: Some(prio), fragment: &b }, 16384, &mut c).unwrap();
    let (rs, ctl) = responses(&run(&c, &[]));
    assert!(rs.is_empty());
    assert!(ctl.contains(&"goaway 1".to_string()), "{ctl:?}");
}

/// `run` with these limits.
fn run_with(limits: Limits2, input: &[u8], cuts: &[usize]) -> Vec<u8> {
    let mut c = Conn2::new(limits);
    let ctx = Ctx::new(b"t", b"Thu, 01 Jan 1970 00:00:00 GMT").unwrap();
    let mut out = Vec::new();
    let mut at = 0;
    for &cut in cuts.iter().chain(std::iter::once(&input.len())) {
        let mut p = &input[at..cut];
        at = cut;
        while !p.is_empty() {
            let b = c.read_buf();
            if b.is_empty() {
                return out;
            }
            let n = b.len().min(p.len());
            b[..n].copy_from_slice(&p[..n]);
            c.filled(n);
            p = &p[n..];
            c.process(&handler, &ctx);
            drain(&mut c, &mut out);
        }
    }
    out
}
