//! HTTP/3 in front: a QUIC client (quinn-proto, with verilith-h3 and
//! verilith-qpack on the client side) asks the proxy, which forwards to an
//! HTTP/1.1 upstream. The client is the one verilith-server's own HTTP/3
//! tests use.
#![cfg(feature = "h3")]
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{SocketAddr, TcpListener, UdpSocket};
use std::os::fd::AsRawFd;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use bytes::{Bytes, BytesMut};
use quinn_proto::{ClientConfig, ConnectionHandle, DatagramEvent, Dir, Endpoint, EndpointConfig, Event, StreamEvent, StreamId};
use rustls::pki_types::CertificateDer;
use verilith_h3::consts::{DATA, HEADERS};
use verilith_h3::{Event as Ev, Reader, Src};
use verilith_qpack::encoder::Encoder;
use verilith_qpack::{Decoder, Fields, Res};
use verilith_proxy::proxy::{Config as ProxyConfig, Proxy, Server as Up};
use verilith_proxy::route::Route;
use verilith_server::{serve, Config};

/// An upstream that answers every request with its method, target and
/// the X-Forwarded-Proto it was sent, slowly for /slow.
fn upstream() -> u16 {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = l.local_addr().unwrap().port();
    std::thread::spawn(move || {
        for s in l.incoming() {
            let Ok(s) = s else { continue };
            std::thread::spawn(move || {
                let mut w = s.try_clone().unwrap();
                let mut r = BufReader::new(s);
                loop {
                    let mut head = String::new();
                    loop {
                        let mut line = String::new();
                        if r.read_line(&mut line).unwrap_or(0) == 0 {
                            return;
                        }
                        head.push_str(&line);
                        if line == "\r\n" {
                            break;
                        }
                    }
                    let cl: usize = head.lines().find_map(|l| l.to_ascii_lowercase().strip_prefix("content-length:").map(|v| v.trim().parse().unwrap())).unwrap_or(0);
                    let mut body = vec![0; cl];
                    r.read_exact(&mut body).unwrap();
                    let mut it = head.split(' ');
                    let (m, t) = (it.next().unwrap().to_string(), it.next().unwrap().to_string());
                    if t == "/slow" {
                        std::thread::sleep(Duration::from_millis(100));
                    }
                    let proto = head.lines().find_map(|l| l.strip_prefix("X-Forwarded-Proto: ")).unwrap_or("-").to_string();
                    let b = if t == "/page" {
                        "<p>a page compressed for HTTP/3 clients</p>\n".repeat(50)
                    } else {
                        format!("{m} {t} {proto} {}", body.len())
                    };
                    let ct = if t == "/page" { "text/html" } else { "text/plain" };
                    let h = format!("HTTP/1.1 200 OK\r\nContent-Type: {ct}\r\nContent-Length: {}\r\n\r\n", b.len());
                    if w.write_all(h.as_bytes()).and_then(|_| w.write_all(b.as_bytes())).is_err() {
                        return;
                    }
                }
            });
        }
    });
    port
}

struct Server {
    addr: SocketAddr,
    roots: Arc<rustls::RootCertStore>,
}

fn server() -> &'static Server {
    static S: OnceLock<Server> = OnceLock::new();
    S.get_or_init(|| {
        let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let cert = CertificateDer::from(c.cert.der().to_vec());
        let key_der = c.signing_key.serialize_der();
        let qc = verilith_server::h3::server_config_der(vec![cert.to_vec()], &key_der, Default::default()).unwrap();
        let port = UdpSocket::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let tcp = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let up = upstream();
        let pc = ProxyConfig {
            upstreams: vec![vec![Up { addr: [127, 0, 0, 1], port: up }]],
            routes: vec![Route { host: None, prefix: vec![], upstream: 0 }],
            ..ProxyConfig::default()
        };
        let cfg = Config { port: tcp, threads: 2, pin: false, h3: Some((port, qc)), ..Config::default() };
        std::thread::spawn(move || serve(cfg, Arc::new(Proxy::new(pc))).unwrap());
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
    #[allow(dead_code)]
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
fn proxied_over_h3() {
    let mut c = Client::connect();
    let (s, _, b) = ok(c.get("/a?b"));
    assert_eq!((s, &b[..]), (200, &b"GET /a?b https 0"[..]));
    // A body, forwarded with its length.
    let req = c.request_bytes("POST", "/p", &[], b"twelve bytes");
    let id = c.send_raw(&req);
    let (s, _, b) = ok(c.response(id));
    assert_eq!((s, &b[..]), (200, &b"POST /p https 12"[..]));
    // Compressed for a client that accepts it.
    let req = c.request_bytes("GET", "/page", &[("accept-encoding", "br")], &[]);
    let id = c.send_raw(&req);
    let (s, f, b) = ok(c.response(id));
    assert_eq!(s, 200);
    assert!(f.iter().any(|(n, v)| n == b"content-encoding" && v == b"br"), "{f:?}");
    let page = verilith_brotli::decompress(&b, 1 << 20).unwrap();
    assert_eq!(page, "<p>a page compressed for HTTP/3 clients</p>\n".repeat(50).as_bytes());
}

#[test]
fn concurrent_streams_answer_out_of_order() {
    let mut c = Client::connect();
    let slow = c.request_bytes("GET", "/slow", &[], &[]);
    let slow = c.send_raw(&slow);
    let ids: Vec<_> = (0..8)
        .map(|i| {
            let b = c.request_bytes("GET", &format!("/s{i}"), &[], &[]);
            c.send_raw(&b)
        })
        .collect();
    for (i, id) in ids.into_iter().enumerate() {
        let (s, _, b) = ok(c.response(id));
        assert_eq!((s, String::from_utf8(b).unwrap()), (200, format!("GET /s{i} https 0")));
    }
    let (s, _, b) = ok(c.response(slow));
    assert_eq!((s, &b[..]), (200, &b"GET /slow https 0"[..]));
}
