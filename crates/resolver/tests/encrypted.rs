//! DNS over TLS and DNS over HTTPS, end to end over sockets, with rustls
//! as the client.
#![cfg(feature = "tls")]
mod hier;

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

use rustls::pki_types::{CertificateDer, ServerName};
use verilith_dns::Message;
use verilith_resolver::service::{self, Options, Resolver};

const PORT: u16 = 10054;

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

struct Setup {
    client: Arc<rustls::ClientConfig>,
    dot: u16,
    doh: u16,
}

fn setup(alpn: &[u8]) -> &'static Setup {
    static S: std::sync::OnceLock<(Vec<u8>, u16, u16)> = std::sync::OnceLock::new();
    let (cert, dot, doh) = S.get_or_init(|| {
        hier::start(PORT);
        let o = Options {
            roots: vec![hier::ROOT.to_vec()],
            upstream_port: PORT,
            timeout: Duration::from_millis(300),
            shards: 4,
            sets: 256,
        };
        let r = Arc::new(Resolver::new(&o));
        let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let dir = std::env::temp_dir().join(format!("vres-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let (cp, kp) = (dir.join("cert.pem"), dir.join("key.pem"));
        std::fs::write(&cp, c.cert.pem()).unwrap();
        std::fs::write(&kp, c.signing_key.serialize_pem()).unwrap();
        let (cp, kp) = (cp.to_str().unwrap().to_string(), kp.to_str().unwrap().to_string());
        let d = Arc::new(service::tls::dot_config(&cp, &kp).unwrap());
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let dot = l.local_addr().unwrap().port();
        service::tls::dot(r.clone(), d, l);
        let (http, doh) = (free_port(), free_port());
        std::thread::spawn(move || service::tls::doh(r, [127, 0, 0, 1], http, doh, &cp, &kp, 4).unwrap());
        for _ in 0..100 {
            if TcpStream::connect(("127.0.0.1", doh)).is_ok() {
                break;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        (c.cert.der().to_vec(), dot, doh)
    });
    let mut roots = rustls::RootCertStore::empty();
    roots.add(CertificateDer::from(cert.clone())).unwrap();
    let p = Arc::new(rustls::crypto::aws_lc_rs::default_provider());
    let mut cl = rustls::ClientConfig::builder_with_provider(p).with_safe_default_protocol_versions().unwrap().with_root_certificates(roots).with_no_client_auth();
    cl.alpn_protocols = vec![alpn.to_vec()];
    Box::leak(Box::new(Setup { client: Arc::new(cl), dot: *dot, doh: *doh }))
}

fn query(id: u16, name: &str) -> Vec<u8> {
    let mut m = Message::new(id, 0x0100);
    m.push_question(name, 1, 1).unwrap();
    m.to_bytes()
}

fn tls(s: &Setup, port: u16) -> rustls::StreamOwned<rustls::ClientConnection, TcpStream> {
    let sock = TcpStream::connect(("127.0.0.1", port)).unwrap();
    sock.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let c = rustls::ClientConnection::new(s.client.clone(), ServerName::try_from("localhost").unwrap()).unwrap();
    rustls::StreamOwned::new(c, sock)
}

fn a_records(reply: &[u8]) -> Vec<Vec<u8>> {
    let m = verilith_dns::parse(reply).unwrap();
    m.answers().filter(|r| r.rtype == 1).map(|r| r.rdata.to_vec()).collect()
}

#[test]
fn dot_pipelined() {
    let s = setup(b"dot");
    let mut t = tls(s, s.dot);
    // Three queries in one write; three replies come back, in any order.
    let mut out = Vec::new();
    for (id, n) in [(1u16, "www.example.com"), (2, "h3.example.com"), (3, "alias.example.com")] {
        let q = query(id, n);
        out.extend_from_slice(&(q.len() as u16).to_be_bytes());
        out.extend(q);
    }
    t.write_all(&out).unwrap();
    let mut seen = Vec::new();
    for _ in 0..3 {
        let mut len = [0u8; 2];
        t.read_exact(&mut len).unwrap();
        let mut r = vec![0u8; u16::from_be_bytes(len) as usize];
        t.read_exact(&mut r).unwrap();
        let m = verilith_dns::parse(&r).unwrap();
        seen.push(m.id());
        match m.id() {
            1 | 3 => assert_eq!(a_records(&r), vec![vec![192, 0, 2, 1], vec![192, 0, 2, 2]]),
            2 => assert_eq!(a_records(&r), vec![vec![10, 0, 0, 3]]),
            _ => panic!(),
        }
    }
    seen.sort();
    assert_eq!(seen, vec![1, 2, 3]);
    assert_eq!(t.conn.alpn_protocol(), Some(&b"dot"[..]));
}

fn http(s: &Setup, req: &[u8]) -> (u16, Vec<u8>, String) {
    let mut t = tls(s, s.doh);
    t.write_all(req).unwrap();
    let mut got = Vec::new();
    let _ = t.read_to_end(&mut got);
    let end = got.windows(4).position(|w| w == b"\r\n\r\n").expect("a response head") + 4;
    let head = String::from_utf8_lossy(&got[..end]).to_string();
    let status = head[9..12].parse().unwrap();
    (status, got[end..].to_vec(), head)
}

#[test]
fn doh_post_and_get() {
    let s = setup(b"http/1.1");
    let q = query(0, "www.example.com");
    let mut req = format!(
        "POST /dns-query HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/dns-message\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        q.len()
    )
    .into_bytes();
    req.extend(&q);
    let (status, body, head) = http(s, &req);
    assert_eq!(status, 200, "{head}");
    assert!(head.to_ascii_lowercase().contains("content-type: application/dns-message"));
    assert!(head.to_ascii_lowercase().contains("cache-control: max-age="));
    assert_eq!(a_records(&body), vec![vec![192, 0, 2, 1], vec![192, 0, 2, 2]]);

    // GET, base64url without padding (RFC 8484 §4.1).
    let q = query(0, "h11.example.com");
    let b64 = base64url(&q);
    let req = format!("GET /dns-query?dns={b64} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    let (status, body, _) = http(s, req.as_bytes());
    assert_eq!(status, 200);
    assert_eq!(a_records(&body), vec![vec![10, 0, 0, 11]]);

    let (status, _, _) = http(s, b"GET /other HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    assert_eq!(status, 404);
    let (status, _, _) = http(s, b"GET /dns-query?dns=%%% HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    assert_eq!(status, 400);
}

fn base64url(b: &[u8]) -> String {
    const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut s = String::new();
    for c in b.chunks(3) {
        let n = (c[0] as u32) << 16 | (*c.get(1).unwrap_or(&0) as u32) << 8 | *c.get(2).unwrap_or(&0) as u32;
        for i in 0..=c.len() {
            s.push(A[(n >> (18 - 6 * i) & 63) as usize] as char);
        }
    }
    s
}
