//! The HTTP/1.1 engine against every way of splitting its input, and its
//! output against verilith-http's response parser.
use verilith_server::h1::{Conn, Ctx, Limits};
use verilith_server::{Field, Request, Response};

fn handler(req: &Request, res: &mut Response) {
    let mut body = Vec::new();
    body.extend_from_slice(req.method);
    body.push(b' ');
    body.extend_from_slice(req.target);
    body.push(b' ');
    body.extend_from_slice(req.body);
    let _ = res.send(200, &[Field { name: b"X-Test", value: b"1" }], &body);
}

fn run(input: &[u8], cuts: &[usize]) -> Vec<u8> {
    let mut c = Conn::new(Limits::default());
    let ctx = Ctx::new(b"t", b"Thu, 01 Jan 1970 00:00:00 GMT").unwrap();
    let mut out = Vec::new();
    let mut at = 0;
    for &cut in cuts.iter().chain(std::iter::once(&input.len())) {
        let piece = &input[at..cut];
        at = cut;
        let mut p = piece;
        while !p.is_empty() {
            let b = c.read_buf();
            if b.is_empty() {
                break;
            }
            let n = b.len().min(p.len());
            b[..n].copy_from_slice(&p[..n]);
            c.filled(n);
            p = &p[n..];
            c.process(&handler, &ctx);
            let w = drain(&mut c);
            out.extend_from_slice(&w);
        }
        if c.closing() {
            break;
        }
    }
    out
}

const MSGS: &[u8] = b"GET /a HTTP/1.1\r\nHost: x\r\n\r\n\
POST /b HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello\
POST /c HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n2;x=y\r\nde\r\n0\r\nT: 1\r\n\r\n\
GET /d HTTP/1.1\r\nHost: x\r\n\r\n";

#[test]
fn split_anywhere_same_output() {
    let whole = run(MSGS, &[]);
    assert_eq!(count(&whole, b"HTTP/1.1 200 OK"), 4);
    for i in 0..=MSGS.len() {
        assert_eq!(run(MSGS, &[i]), whole, "split at {i}");
    }
    for i in (0..=MSGS.len()).step_by(7) {
        for j in i..=MSGS.len() {
            assert_eq!(run(MSGS, &[i, j]), whole, "split at {i}, {j}");
        }
    }
    let ones: Vec<usize> = (1..MSGS.len()).collect();
    assert_eq!(run(MSGS, &ones), whole, "one byte at a time");
}

fn drain(c: &mut Conn) -> Vec<u8> {
    let mut w = Vec::new();
    let mut v: [&[u8]; 8] = [&[]; 8];
    let k = c.pending(&mut v);
    for s in &v[..k] {
        w.extend_from_slice(s);
    }
    c.wrote(w.len());
    w
}

fn count(h: &[u8], n: &[u8]) -> usize {
    h.windows(n.len()).filter(|w| *w == n).count()
}

/// Every response parses, with verilith-http, to what the handler sent, and
/// they come in request order.
#[test]
fn responses_parse_back_in_order() {
    let out = run(MSGS, &[]);
    let mut rest = &out[..];
    let mut bodies = Vec::new();
    let mut hs = Vec::new();
    while !rest.is_empty() {
        match verilith_http::parse_response(rest, false, false, &mut hs).unwrap() {
            verilith_http::Status::Complete(r) => {
                assert_eq!(r.status(), 200);
                let fields: Vec<_> = r.headers(&hs).map(|(n, v)| (n.to_vec(), v.to_vec())).collect();
                assert_eq!(fields[2], (b"X-Test".to_vec(), b"1".to_vec()));
                let verilith_http::Body::Length(n) = r.body else { panic!() };
                let b = &rest[r.head_len..r.head_len + n as usize];
                bodies.push(b.to_vec());
                rest = &rest[r.head_len + n as usize..];
            }
            _ => panic!("partial response"),
        }
    }
    assert_eq!(bodies, vec![b"GET /a ".to_vec(), b"POST /b hello".to_vec(), b"POST /c abcde".to_vec(), b"GET /d ".to_vec()]);
}

#[test]
fn smuggling_shapes_close_the_connection() {
    for bad in [
        &b"POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\nGET /smuggled HTTP/1.1\r\nHost: x\r\n\r\n"[..],
        b"POST / HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nContent-Length: 4\r\n\r\nabcdGET /smuggled HTTP/1.1\r\nHost: x\r\n\r\n",
        b"POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n3\nabc\r\n0\r\n\r\nGET /smuggled HTTP/1.1\r\nHost: x\r\n\r\n",
        b"GET / HTTP/1.1\r\nHost: x\r\n Folded: y\r\n\r\nGET /smuggled HTTP/1.1\r\nHost: x\r\n\r\n",
    ] {
        let out = run(bad, &[]);
        assert!(out.starts_with(b"HTTP/1.1 400"), "{}", String::from_utf8_lossy(&out));
        assert_eq!(count(&out, b"HTTP/1.1"), 1);
        assert!(count(&out, b"Connection: close") == 1);
    }
}

#[test]
fn http10_and_close() {
    let out = run(b"GET /a HTTP/1.0\r\n\r\nGET /b HTTP/1.1\r\nHost: x\r\n\r\n", &[]);
    assert_eq!(count(&out, b"HTTP/1.1 200"), 1);
    assert!(count(&out, b"Connection: close") == 1);
    let out = run(b"GET /a HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\nGET /b HTTP/1.1\r\nHost: x\r\n\r\n", &[]);
    assert_eq!(count(&out, b"HTTP/1.1 200"), 1);
    let out = run(b"GET /a HTTP/1.0\r\nConnection: keep-alive\r\n\r\nGET /b HTTP/1.1\r\nHost: x\r\n\r\n", &[]);
    assert_eq!(count(&out, b"HTTP/1.1 200"), 2);
    // Options are list elements, any case, OWS trimmed, on any Connection line.
    for c in ["Connection: keep-alive, CLOSE", "Connection: ,  Close  ,", "X: 1\r\nconnection: upgrade\r\nCONNECTION: close"] {
        let req = format!("GET /a HTTP/1.1\r\nHost: x\r\n{c}\r\n\r\nGET /b HTTP/1.1\r\nHost: x\r\n\r\n");
        assert_eq!(count(&run(req.as_bytes(), &[]), b"HTTP/1.1 200"), 1, "{c}");
    }
    for c in ["Connection: closed", "Connection: keep-alive", "Connection: close-ish", "X-Connection: close"] {
        let req = format!("GET /a HTTP/1.1\r\nHost: x\r\n{c}\r\n\r\nGET /b HTTP/1.1\r\nHost: x\r\n\r\n");
        assert_eq!(count(&run(req.as_bytes(), &[]), b"HTTP/1.1 200"), 2, "{c}");
    }
    let out = run(b"GET /a HTTP/1.0\r\nConnection: Keep-Alive\r\n\r\nGET /b HTTP/1.0\r\n\r\nGET /c HTTP/1.1\r\n\r\n", &[]);
    assert_eq!(count(&out, b"HTTP/1.1 200"), 2);
}

#[test]
fn head_has_no_body() {
    let out = run(b"HEAD /a HTTP/1.1\r\nHost: x\r\n\r\nGET /b HTTP/1.1\r\nHost: x\r\n\r\n", &[]);
    let s = String::from_utf8_lossy(&out);
    assert!(s.contains("Content-Length: 8\r\n\r\nHTTP/1.1 200"), "{s}");
}

#[test]
fn handler_cannot_split_a_response() {
    fn evil(_: &Request, res: &mut Response) {
        assert!(res.send(200, &[Field { name: b"X", value: b"a\r\nContent-Length: 0" }], b"x").is_err());
        assert!(res.send(200, &[Field { name: b"Content-Length", value: b"0" }], b"x").is_err());
        assert!(res.send(200, &[Field { name: b"Content_Length", value: b"0" }], b"x").is_err());
        assert!(res.send(200, &[Field { name: b"Bad Name", value: b"0" }], b"x").is_err());
        assert!(res.send(200, &[], b"ok").is_ok());
    }
    let mut c = Conn::new(Limits::default());
    let ctx = Ctx::new(b"t", b"d").unwrap();
    let m = b"GET / HTTP/1.1\r\nHost: x\r\n\r\n";
    c.read_buf()[..m.len()].copy_from_slice(m);
    c.filled(m.len());
    c.process(&evil, &ctx);
    assert!(drain(&mut c).ends_with(b"Content-Length: 2\r\n\r\nok"));
}

#[test]
fn too_large_head() {
    let mut big = b"GET / HTTP/1.1\r\nHost: x\r\nX: ".to_vec();
    big.resize(20000, b'a');
    let out = run(&big, &[]);
    assert!(out.starts_with(b"HTTP/1.1 431"));
}

/// Static bodies: what the event loop sends (slices, and file ranges by
/// `sendfile`) is byte for byte what the in-memory view says, across
/// pipelined responses and partial writes.
#[test]
fn static_bodies_by_file_match_memory() {
    use std::sync::Arc;
    use verilith_server::h1::Io;
    use verilith_server::{Fields, StaticBody};
    let big: Vec<u8> = (0..40_000u32).map(|i| (i * 7 % 251) as u8).collect();
    let body = Arc::new(StaticBody::new(big.clone()));
    let f = Fields::new(&[Field { name: b"Content-Type", value: b"application/octet-stream" }]).unwrap();
    let b2 = body.clone();
    let h = move |req: &Request, res: &mut Response| {
        if req.target == b"/big" {
            let _ = res.send_static(200, &f, &b2);
        } else {
            let _ = res.send(200, &[], b"small");
        }
    };
    let input = b"GET /big HTTP/1.1\r\nHost: x\r\n\r\nGET /s HTTP/1.1\r\nHost: x\r\n\r\nGET /big HTTP/1.1\r\nHost: x\r\n\r\nHEAD /big HTTP/1.1\r\nHost: x\r\n\r\n";
    let ctx = Ctx::new(b"t", b"Thu, 01 Jan 1970 00:00:00 GMT").unwrap();
    let feed = |c: &mut Conn| {
        let b = c.read_buf();
        b[..input.len()].copy_from_slice(input);
        c.filled(input.len());
        c.process(&h, &ctx);
    };
    // Reference: the in-memory view.
    let mut c = Conn::new(Limits::default());
    feed(&mut c);
    let mut mem = Vec::new();
    while c.pending_len() > 0 {
        mem.extend(drain(&mut c));
    }
    assert_eq!(count(&mem, b"HTTP/1.1 200 OK"), 4);
    assert!(mem.windows(big.len()).filter(|w| *w == &big[..]).count() == 2);
    // The event loop's view, writing at most 3000 bytes per call.
    let mut c = Conn::new(Limits::default());
    feed(&mut c);
    let mut wire = Vec::new();
    let mut files = 0;
    while c.pending_len() > 0 {
        let mut v: [&[u8]; 8] = [&[]; 8];
        let mut more = false;
        let n = match c.pending_io(&mut v, &mut more) {
            Io::Slices(k, _) => {
                let mut n = 0;
                for s in &v[..k] {
                    let t = s.len().min(3000 - n);
                    wire.extend_from_slice(&s[..t]);
                    n += t;
                    if n == 3000 {
                        break;
                    }
                }
                n
            }
            Io::File { fd, off, len } => {
                files += 1;
                let all = std::fs::read(format!("/proc/self/fd/{fd}")).unwrap();
                let t = len.min(3000);
                wire.extend_from_slice(&all[off..off + t]);
                t
            }
        };
        c.wrote(n);
    }
    assert_eq!(wire, mem);
    if cfg!(target_os = "linux") {
        assert!(files > 0);
    }
}

#[test]
fn alt_svc_on_every_response() {
    fn h(_: &Request, res: &mut Response) {
        let _ = res.send(200, &[], b"ok");
    }
    let mut c = Conn::new(Limits::default());
    let ctx = Ctx::with_alt_svc(b"t", b"d", Some(b"h3=\":443\"; ma=86400")).unwrap();
    let m = b"GET / HTTP/1.1\r\nHost: x\r\n\r\nGET / HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
    c.read_buf()[..m.len()].copy_from_slice(m);
    c.filled(m.len());
    c.process(&h, &ctx);
    let out = String::from_utf8(drain(&mut c)).unwrap();
    assert_eq!(out.matches("Alt-Svc: h3=\":443\"; ma=86400\r\n").count(), 2, "{out}");
    assert!(Ctx::with_alt_svc(b"t", b"d", Some(b"bad\r\nX: y")).is_none());
}
