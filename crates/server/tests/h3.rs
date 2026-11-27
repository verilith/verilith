//! HTTP/3: a QUIC client (quinn-proto, with verilith-h3 and verilith-qpack
//! on the client side) talks to the server over UDP on 127.0.0.1.
#![cfg(feature = "h3")]
use std::net::{SocketAddr, UdpSocket};
use std::os::fd::AsRawFd;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use bytes::{Bytes, BytesMut};
use quinn_proto::{ClientConfig, ConnectionHandle, DatagramEvent, Dir, Endpoint, EndpointConfig, Event, StreamEvent, StreamId, VarInt};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use verilith_h3::consts::{DATA, HEADERS};
use verilith_h3::{Event as Ev, Reader, Src};
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};
use verilith_server::h3::Limits3;
use verilith_server::{serve, Config, Field, Request, Response};

fn handler(req: &Request, res: &mut Response) {
    match req.path() {
        b"/big" => {
            let body: Vec<u8> = (0..3_000_000u32).map(|i| (i % 251) as u8).collect();
            let _ = res.send(200, &[], &body);
        }
        b"/echo" => {
            let _ = res.send(200, &[Field { name: b"X-Len", value: req.body.len().to_string().as_bytes() }], req.body);
        }
        _ => {
            let mut b = req.method.to_vec();
            b.push(b' ');
            b.extend_from_slice(req.target);
            let _ = res.send(200, &[Field { name: b"X-Test", value: b"1" }], &b);
        }
    }
}

struct Server {
    addr: SocketAddr,
    roots: Arc<rustls::RootCertStore>,
}

/// A server on each QUIC backend.
fn server() -> &'static Server {
    static S: OnceLock<Server> = OnceLock::new();
    S.get_or_init(|| {
        let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let cert = CertificateDer::from(c.cert.der().to_vec());
        let key_der = c.signing_key.serialize_der();
        let qc = verilith_server::h3::server_config_der(vec![cert.to_vec()], &key_der, Limits3 { max_body: 100_000, ..Limits3::default() }).unwrap();
        let port = UdpSocket::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let tcp = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let cfg = Config {
            port: tcp,
            threads: 2,
            pin: false,
            h3: Some((port, qc)),
            limits3: Limits3 { max_body: 100_000, ..Limits3::default() },
            ..Config::default()
        };
        std::thread::spawn(move || serve(cfg, Arc::new(handler)).unwrap());
        std::thread::sleep(Duration::from_millis(100));
        let mut roots = rustls::RootCertStore::empty();
        roots.add(cert).unwrap();
        Server { addr: SocketAddr::from(([127, 0, 0, 1], port)), roots: Arc::new(roots) }
    })
}

/// A response: status, fields, body; or the stream's reset code.
#[derive(Debug)]
enum Got {
    Ok(u16, Vec<(Vec<u8>, Vec<u8>)>, Vec<u8>),
    Reset(u64),
}

struct Client {
    sock: UdpSocket,
    ep: Endpoint,
    ch: ConnectionHandle,
    q: quinn_proto::Connection,
    dec: Decoder,
    enc: Encoder,
    server: SocketAddr,
    lost: Option<quinn_proto::ConnectionError>,
    gso: bool,
}

impl Client {
    fn connect() -> Client {
        let s = server();
        let mut cl = rustls::ClientConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
            .with_protocol_versions(&[&rustls::version::TLS13])
            .unwrap()
            .with_root_certificates(s.roots.clone())
            .with_no_client_auth();
        cl.alpn_protocols = vec![b"h3".to_vec()];
        let cc = ClientConfig::new(Arc::new(quinn_proto::crypto::rustls::QuicClientConfig::try_from(cl).unwrap()));
        let sock = UdpSocket::bind("127.0.0.1:0").unwrap();
        sock.set_read_timeout(Some(Duration::from_millis(5))).unwrap();
        let mut ep = Endpoint::new(Arc::new(EndpointConfig::default()), None, true, None);
        let (ch, q) = ep.connect(Instant::now(), cc, s.addr, "localhost").unwrap();
        let mut c = Client { sock, ep, ch, q, dec: Decoder::new(0, 0, 1 << 16).unwrap(), enc: Encoder::new(0, 0, 0).unwrap(), server: s.addr, lost: None, gso: true };
        let t = Instant::now();
        while c.q.is_handshaking() {
            assert!(t.elapsed() < Duration::from_secs(5), "handshake timed out");
            c.step();
        }
        c
    }

    /// Sends what quinn has, then waits a little for one datagram.
    fn step(&mut self) {
        let now = Instant::now();
        let mut buf = Vec::new();
        // Batches of datagrams with segmentation offload where the kernel
        // has it, so the server's receive offload path is exercised.
        while let Some(t) = self.q.poll_transmit(now, 10, &mut buf) {
            let SocketAddr::V4(d) = t.destination else { unreachable!() };
            let seg = t.segment_size.unwrap_or(t.size);
            verilith_server::sys::send_to(self.sock.as_raw_fd(), &buf[..t.size], d.ip().octets(), d.port(), seg, &mut self.gso);
            buf.clear();
        }
        let mut rb = [0u8; 65536];
        if let Ok((n, from)) = self.sock.recv_from(&mut rb) {
            if let Some(DatagramEvent::ConnectionEvent(_, ev)) = self.ep.handle(Instant::now(), from, None, None, BytesMut::from(&rb[..n]), &mut buf) {
                self.q.handle_event(ev);
            }
        }
        if let Some(t) = self.q.poll_timeout() {
            if t <= Instant::now() {
                self.q.handle_timeout(Instant::now());
            }
        }
        while let Some(ev) = self.q.poll_endpoint_events() {
            if let Some(back) = self.ep.handle_event(self.ch, ev) {
                self.q.handle_event(back);
            }
        }
        // Peer-initiated uni streams (the server's control stream): accept
        // and drain them.
        while let Some(e) = self.q.poll() {
            match e {
                Event::Stream(StreamEvent::Opened { dir: Dir::Uni }) => while self.q.streams().accept(Dir::Uni).is_some() {},
                Event::ConnectionLost { reason } => self.lost = Some(reason),
                _ => {}
            }
        }
    }

    /// Sends a request with these fields and body on a new stream, using
    /// `frames` to build its bytes (to send malformed ones).
    fn send_raw(&mut self, bytes: &[u8]) -> StreamId {
        let t = Instant::now();
        let id = loop {
            if let Some(id) = self.q.streams().open(Dir::Bi) {
                break id;
            }
            // Out of stream credit: wait for the server to grant more.
            assert!(t.elapsed() < Duration::from_secs(5) && self.lost.is_none(), "no stream credit");
            self.step();
        };
        let mut s = self.q.send_stream(id);
        let mut off = 0;
        while off < bytes.len() {
            match s.write(&bytes[off..]) {
                Ok(n) => off += n,
                Err(_) => {
                    self.step();
                    s = self.q.send_stream(id);
                }
            }
        }
        self.q.send_stream(id).finish().unwrap();
        id
    }

    fn request_bytes(&mut self, method: &str, path: &str, extra: &[(&str, &str)], body: &[u8]) -> Vec<u8> {
        let mut f = Fields::new();
        f.push(b":method", method.as_bytes(), false);
        f.push(b":scheme", b"https", false);
        f.push(b":authority", b"localhost", false);
        f.push(b":path", path.as_bytes(), false);
        for (n, v) in extra {
            f.push(n.as_bytes(), v.as_bytes(), false);
        }
        let mut sec = Vec::new();
        self.enc.encode(0, &f, &mut sec);
        frames(&sec, body)
    }

    /// Reads a stream's response until it ends.
    fn response(&mut self, id: StreamId) -> Got {
        let mut r = Reader::new_request(false, 1 << 16);
        let mut status = 0;
        let mut fields = Vec::new();
        let mut body = Vec::new();
        let t = Instant::now();
        loop {
            assert!(t.elapsed() < Duration::from_secs(10), "response timed out");
            let mut rs = self.q.recv_stream(id);
            let mut chunks = rs.read(true).unwrap();
            let mut fin = false;
            let mut pieces: Vec<Bytes> = Vec::new();
            loop {
                match chunks.next(usize::MAX) {
                    Ok(Some(c)) => pieces.push(c.bytes),
                    Ok(None) => {
                        fin = true;
                        break;
                    }
                    Err(quinn_proto::ReadError::Blocked) => break,
                    Err(quinn_proto::ReadError::Reset(code)) => {
                        let _ = chunks.finalize();
                        return Got::Reset(code.into_inner());
                    }
                }
            }
            let _ = chunks.finalize();
            if fin {
                pieces.push(Bytes::new());
            }
            let n = pieces.len();
            for (k, p) in pieces.into_iter().enumerate() {
                let last = fin && k == n - 1;
                let mut input: &[u8] = &p;
                loop {
                    let (ev, used) = r.next(input, last);
                    match ev {
                        Ev::Need => break,
                        Ev::End => return Got::Ok(status, fields, body),
                        Ev::Error(e) => panic!("response stream error {e:#x}"),
                        Ev::Headers(src) => {
                            let sec = match src {
                                Src::Input(a, b) => input[a..b].to_vec(),
                                Src::Buf(o) => r.buffered()[o..].to_vec(),
                            };
                            let mut out = Fields::new();
                            assert!(matches!(self.dec.decode(u64::from(id), &sec, &mut out), Res::Done));
                            for i in 0..out.len() {
                                let (n, v, _) = out.get(i);
                                if n == b":status" {
                                    status = std::str::from_utf8(v).unwrap().parse().unwrap();
                                } else {
                                    fields.push((n.to_vec(), v.to_vec()));
                                }
                            }
                        }
                        Ev::Data(a, b) => body.extend_from_slice(&input[a..b]),
                        _ => {}
                    }
                    input = &input[used..];
                }
            }
            self.step();
        }
    }

    fn get(&mut self, path: &str) -> Got {
        let b = self.request_bytes("GET", path, &[], &[]);
        let id = self.send_raw(&b);
        self.response(id)
    }
}

/// HEADERS with this section, then DATA with this body if any.
fn frames(sec: &[u8], body: &[u8]) -> Vec<u8> {
    let mut b = [0u8; 16];
    let mut out = Vec::new();
    let n = verilith_h3::write_header(&mut b, 0, HEADERS, sec.len() as u64).unwrap();
    out.extend_from_slice(&b[..n]);
    out.extend_from_slice(sec);
    if !body.is_empty() {
        let n = verilith_h3::write_header(&mut b, 0, DATA, body.len() as u64).unwrap();
        out.extend_from_slice(&b[..n]);
        out.extend_from_slice(body);
    }
    out
}

fn ok(g: Got) -> (u16, Vec<(Vec<u8>, Vec<u8>)>, Vec<u8>) {
    match g {
        Got::Ok(s, f, b) => (s, f, b),
        Got::Reset(c) => panic!("stream reset {c:#x}"),
    }
}

#[test]
fn get_and_head() {
    let mut c = Client::connect();
    let (s, f, b) = ok(c.get("/a?b"));
    assert_eq!((s, &b[..]), (200, &b"GET /a?b"[..]));
    assert!(f.iter().any(|(n, v)| n == b"x-test" && v == b"1"), "{f:?}");
    assert!(f.iter().any(|(n, _)| n == b"server"));
    assert!(f.iter().any(|(n, v)| n == b"content-length" && v == b"8"));
    let req = c.request_bytes("HEAD", "/x", &[], &[]);
    let id = c.send_raw(&req);
    let (s, f, b) = ok(c.response(id));
    assert_eq!((s, b.len()), (200, 0));
    assert!(f.iter().any(|(n, v)| n == b"content-length" && v == b"7"));
}

#[test]
fn many_streams_one_connection() {
    let mut c = Client::connect();
    let ids: Vec<_> = (0..200).map(|i| {
        let b = c.request_bytes("GET", &format!("/{i}"), &[], &[]);
        (i, c.send_raw(&b))
    }).collect();
    for (i, id) in ids {
        let (s, _, b) = ok(c.response(id));
        assert_eq!((s, b), (200, format!("GET /{i}").into_bytes()));
    }
}

#[test]
fn large_response_body() {
    let mut c = Client::connect();
    let (s, _, b) = ok(c.get("/big"));
    assert_eq!(s, 200);
    assert_eq!(b.len(), 3_000_000);
    assert!(b.iter().enumerate().all(|(i, &x)| x == (i % 251) as u8));
}

#[test]
fn request_bodies() {
    let mut c = Client::connect();
    let body: Vec<u8> = (0..50_000u32).map(|i| i as u8).collect();
    let req = c.request_bytes("POST", "/echo", &[("content-type", "x/y")], &body);
    let id = c.send_raw(&req);
    let (s, f, b) = ok(c.response(id));
    assert_eq!((s, &b), (200, &body));
    assert!(f.iter().any(|(n, v)| n == b"x-len" && v == b"50000"));
    // Over the server's 100,000-byte limit.
    let big = vec![7u8; 150_000];
    let req = c.request_bytes("POST", "/echo", &[], &big);
    let id = c.send_raw(&req);
    assert_eq!(ok(c.response(id)).0, 413);
}

#[test]
fn malformed_requests_are_reset() {
    let mut c = Client::connect();
    // No :path.
    let mut f = Fields::new();
    f.push(b":method", b"GET", false);
    f.push(b":scheme", b"https", false);
    let mut sec = Vec::new();
    c.enc.encode(0, &f, &mut sec);
    let id = c.send_raw(&frames(&sec, &[]));
    assert!(matches!(c.response(id), Got::Reset(0x10e)), "H3_MESSAGE_ERROR");
    // An uppercase name and a connection-specific field.
    for (n, v) in [("X-Upper", "1"), ("connection", "close")] {
        let b = c.request_bytes("GET", "/", &[(n, v)], &[]);
        let id = c.send_raw(&b);
        assert!(matches!(c.response(id), Got::Reset(0x10e)), "{n}");
    }
    // The connection still works.
    assert_eq!(ok(c.get("/after")).2, b"GET /after");
}

#[test]
fn frame_errors_close_the_connection() {
    let mut c = Client::connect();
    // DATA before HEADERS: H3_FRAME_UNEXPECTED (§4.1).
    c.send_raw(&[0x00, 0x01, b'x']);
    let t = Instant::now();
    while c.lost.is_none() {
        c.step();
        assert!(t.elapsed() < Duration::from_secs(5), "not closed");
    }
    match c.lost.take().unwrap() {
        quinn_proto::ConnectionError::ApplicationClosed(a) => assert_eq!(a.error_code, VarInt::from_u32(0x105)),
        e => panic!("{e:?}"),
    }
    let _ = c.server;
}

/// Requests one after another on one connection reuse the server's stream
/// state: each response has its own fields, once.
#[test]
fn sequential_requests_reuse_stream_state() {
    let mut c = Client::connect();
    for i in 0..20 {
        let (s, f, b) = ok(c.get(&format!("/seq{i}")));
        assert_eq!((s, b), (200, format!("GET /seq{i}").into_bytes()));
        for name in [&b"content-length"[..], b"x-test", b"server", b"date", b"content-type"] {
            assert!(f.iter().filter(|(n, _)| n == name).count() <= 1, "{i}: {f:?}");
        }
    }
}

impl Client {
    /// Opens a unidirectional stream with these bytes; finishes it if
    /// `fin`.
    fn send_uni(&mut self, bytes: &[u8], fin: bool) -> StreamId {
        let id = self.q.streams().open(Dir::Uni).unwrap();
        assert_eq!(self.q.send_stream(id).write(bytes).unwrap(), bytes.len());
        if fin {
            self.q.send_stream(id).finish().unwrap();
        }
        id
    }

    /// Waits for the server to close the connection; its error code.
    fn closed(&mut self) -> u64 {
        let t = Instant::now();
        while self.lost.is_none() {
            self.step();
            assert!(t.elapsed() < Duration::from_secs(5), "not closed");
        }
        match self.lost.take().unwrap() {
            quinn_proto::ConnectionError::ApplicationClosed(a) => a.error_code.into_inner(),
            e => panic!("{e:?}"),
        }
    }
}

/// Content-Length must match the DATA (RFC 9114 §4.1.2), and be a
/// length.
#[test]
fn content_length_checked() {
    let mut c = Client::connect();
    for (cl, body) in [("5", &b"abc"[..]), ("2", b"abc"), ("x", b"abc"), ("3, 3", b"abc"), ("1", b"")] {
        let req = c.request_bytes("POST", "/echo", &[("content-length", cl)], body);
        let id = c.send_raw(&req);
        assert!(matches!(c.response(id), Got::Reset(0x10e)), "content-length {cl:?} with {} bytes", body.len());
    }
    // Two that agree, and one that matches.
    let req = c.request_bytes("POST", "/echo", &[("content-length", "3"), ("content-length", "3")], b"abc");
    let id = c.send_raw(&req);
    assert_eq!(ok(c.response(id)).2, b"abc");
    let req = c.request_bytes("POST", "/echo", &[("content-length", "3")], b"abc");
    let id = c.send_raw(&req);
    assert_eq!(ok(c.response(id)).2, b"abc");
}

/// Trailers are decoded (for their errors) and not passed on.
#[test]
fn trailers_ignored() {
    let mut c = Client::connect();
    let mut req = c.request_bytes("POST", "/echo", &[], b"hi");
    let mut f = Fields::new();
    f.push(b"x-trailer", b"1", false);
    let mut sec = Vec::new();
    c.enc.encode(0, &f, &mut sec);
    req.extend_from_slice(&frames(&sec, &[]));
    let id = c.send_raw(&req);
    assert_eq!(ok(c.response(id)).2, b"hi");
}

/// A second control stream (§6.2.1): H3_STREAM_CREATION_ERROR.
#[test]
fn second_control_stream() {
    let mut c = Client::connect();
    c.send_uni(&[0x00, 0x04, 0x00], false);
    c.send_uni(&[0x00, 0x04, 0x00], false);
    assert_eq!(c.closed(), 0x103);
}

/// The control stream or a QPACK stream ending (§6.2.1, RFC 9204 §4.2):
/// H3_CLOSED_CRITICAL_STREAM.
#[test]
fn critical_stream_closed() {
    for bytes in [&[0x00u8, 0x04, 0x00][..], &[0x02], &[0x03]] {
        let mut c = Client::connect();
        c.send_uni(bytes, true);
        assert_eq!(c.closed(), 0x104, "{bytes:?}");
    }
}

/// A stream of an unknown type is ignored (§6.2.3), and the connection
/// still works.
#[test]
fn unknown_uni_stream() {
    let mut c = Client::connect();
    c.send_uni(&[0x21, 1, 2, 3], true);
    assert_eq!(ok(c.get("/after")).2, b"GET /after");
}

/// A client that only sends requests the server refuses is cut off: at
/// most `2 * max_streams` plus 100 per completed request
/// (H3_EXCESSIVE_LOAD).
#[test]
fn abandoned_requests_flood() {
    let mut c = Client::connect();
    assert_eq!(ok(c.get("/first")).0, 200);
    let bad = c.request_bytes("GET", "/", &[("X-Upper", "1")], &[]);
    for _ in 0..(2 * 256 + 100) {
        c.send_raw(&bad);
        c.step();
    }
    // Over the budget: the next refusal closes the connection.
    for _ in 0..16 {
        if c.lost.is_some() {
            break;
        }
        c.send_raw(&bad);
        c.step();
    }
    assert_eq!(c.closed(), 0x107);
}
