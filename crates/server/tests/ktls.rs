//! kTLS (Linux): a server with `ktls` on, over real sockets, against a
//! rustls client. Where the kernel has kTLS (the `tls` module), the
//! kernel seals what the server sends once the handshake is over, and
//! static bodies go out with `sendfile`; where it has none, the same
//! connections stay in userspace. Either way every response must arrive
//! whole and in order, a client's KeyUpdate must be answered, and the
//! connection must end with a close_notify.
//!
//! `VERILITH_REQUIRE_KTLS=1` fails the run unless the kernel counted the
//! connections as its own (`/proc/net/tls_stat`): the check for a machine
//! that is meant to have kTLS.
#![cfg(all(target_os = "linux", feature = "tls"))]
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use rustls::pki_types::{CertificateDer, ServerName};
use verilith_server::h1::StaticBody;
use verilith_server::{serve, Config, Fields, Request, Response};

fn big() -> &'static [u8] {
    static B: OnceLock<Vec<u8>> = OnceLock::new();
    B.get_or_init(|| (0..300_000u32).map(|i| (i * 7 + i / 251) as u8).collect())
}

fn statics() -> &'static (StaticBody, StaticBody, StaticBody) {
    static S: OnceLock<(StaticBody, StaticBody, StaticBody)> = OnceLock::new();
    S.get_or_init(|| {
        // 64 KiB: sendfile from a sealed memfd; 1 MiB: writev from memory;
        // 1 MiB again, with sendfile.
        let huge: Vec<u8> = (0..1 << 20).map(|i: u32| (i % 253) as u8).collect();
        (StaticBody::new(big()[..65536].to_vec()), StaticBody::new(huge.clone()), StaticBody::with_sendfile(huge, true))
    })
}

fn expect(path: &str) -> Vec<u8> {
    match path {
        "/plaintext" => b"Hello, World!".to_vec(),
        "/big" => big().to_vec(),
        "/mid" => big()[..65536].to_vec(),
        "/huge" | "/huge-sf" => (0..1 << 20).map(|i: u32| (i % 253) as u8).collect(),
        _ => unreachable!(),
    }
}

fn handler(req: &Request, res: &mut Response) {
    let f = Fields::new(&[]).unwrap();
    let (mid, huge, huge_sf) = statics();
    let _ = match req.path() {
        b"/plaintext" => res.send_prepared(200, &f, b"Hello, World!"),
        b"/big" => res.send_prepared(200, &f, big()),
        b"/mid" => res.send_static(200, &f, mid),
        b"/huge" => res.send_static(200, &f, huge),
        b"/huge-sf" => res.send_static(200, &f, huge_sf),
        _ => {
            res.error(404);
            Ok(())
        }
    };
}

/// The server's TLS port and the client configuration that trusts it.
fn server() -> &'static (u16, rustls::RootCertStore) {
    static S: OnceLock<(u16, rustls::RootCertStore)> = OnceLock::new();
    S.get_or_init(|| {
        let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let tls = verilith_server::tls::config_der(vec![c.cert.der().to_vec()], &c.signing_key.serialize_der()).unwrap();
        let port = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let http = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let cfg = Config { port: http, threads: 2, pin: false, tls: Some((port, tls)), ktls: true, ..Config::default() };
        std::thread::spawn(move || serve(cfg, Arc::new(handler)));
        for _ in 0..500 {
            if TcpStream::connect(("127.0.0.1", port)).is_ok() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        let mut roots = rustls::RootCertStore::empty();
        roots.add(CertificateDer::from(c.cert.der().to_vec())).unwrap();
        (port, roots)
    })
}

type Stream = rustls::StreamOwned<rustls::ClientConnection, TcpStream>;

fn connect(suite: Option<rustls::SupportedCipherSuite>, alpn: &[u8]) -> Stream {
    let (port, roots) = server();
    let mut p = rustls::crypto::aws_lc_rs::default_provider();
    if let Some(s) = suite {
        p.cipher_suites = vec![s];
    }
    let mut cl = rustls::ClientConfig::builder_with_provider(Arc::new(p))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots.clone())
        .with_no_client_auth();
    cl.alpn_protocols = vec![alpn.to_vec()];
    // A fresh handshake each time, not a resumption.
    cl.resumption = rustls::client::Resumption::disabled();
    let conn = rustls::ClientConnection::new(Arc::new(cl), ServerName::try_from("localhost").unwrap()).unwrap();
    let sock = TcpStream::connect(("127.0.0.1", *port)).unwrap();
    sock.set_read_timeout(Some(Duration::from_secs(20))).unwrap();
    rustls::StreamOwned::new(conn, sock)
}

/// Reads one response with a Content-Length body: (status line, body).
fn response(s: &mut Stream) -> (String, Vec<u8>) {
    let mut head = Vec::new();
    let mut b = [0u8; 1];
    while !head.ends_with(b"\r\n\r\n") {
        s.read_exact(&mut b).expect("response head");
        head.push(b[0]);
    }
    let h = String::from_utf8(head).unwrap();
    let len: usize = h
        .lines()
        .find_map(|l| l.to_ascii_lowercase().strip_prefix("content-length:").map(|v| v.trim().parse().unwrap()))
        .expect("Content-Length");
    let mut body = vec![0u8; len];
    s.read_exact(&mut body).expect("response body");
    (h.lines().next().unwrap().to_string(), body)
}

fn get(s: &mut Stream, path: &str, close: bool) {
    let c = if close { "Connection: close\r\n" } else { "" };
    s.write_all(format!("GET {path} HTTP/1.1\r\nHost: x\r\n{c}\r\n").as_bytes()).unwrap();
    s.flush().unwrap();
    let (status, body) = response(s);
    assert_eq!(status, "HTTP/1.1 200 OK", "{path}");
    assert!(body == expect(path), "{path}: {} bytes, not the {} expected", body.len(), expect(path).len());
}

/// The kernel's count of TLS connections it has sealed for (software).
fn tls_tx_count() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/net/tls_stat").ok()?;
    s.lines().find_map(|l| l.strip_prefix("TlsTxSw").map(|v| v.trim().parse().unwrap()))
}

fn ends_cleanly(s: &mut Stream) {
    let mut rest = Vec::new();
    // rustls reports a close without close_notify as UnexpectedEof.
    s.read_to_end(&mut rest).expect("close_notify, then EOF");
    assert!(rest.is_empty(), "{} bytes after the last response", rest.len());
}

#[test]
fn ktls_http11_every_suite() {
    use rustls::crypto::aws_lc_rs::cipher_suite::*;
    let before = tls_tx_count();
    for suite in [TLS13_AES_128_GCM_SHA256, TLS13_AES_256_GCM_SHA384, TLS13_CHACHA20_POLY1305_SHA256] {
        let mut s = connect(Some(suite), b"http/1.1");
        // The first response may still be sealed in userspace (it can
        // leave with the session tickets); the rest are the kernel's.
        for p in ["/plaintext", "/mid", "/huge", "/huge-sf", "/big", "/plaintext", "/mid"] {
            get(&mut s, p, false);
        }
        // Pipelined: several responses in one write.
        s.write_all(b"GET /mid HTTP/1.1\r\nHost: x\r\n\r\nGET /plaintext HTTP/1.1\r\nHost: x\r\n\r\nGET /huge-sf HTTP/1.1\r\nHost: x\r\n\r\n").unwrap();
        for p in ["/mid", "/plaintext", "/huge-sf"] {
            let (st, body) = response(&mut s);
            assert_eq!(st, "HTTP/1.1 200 OK");
            assert!(body == expect(p), "pipelined {p}");
        }
        get(&mut s, "/mid", true);
        ends_cleanly(&mut s);
    }
    let after = tls_tx_count();
    eprintln!("kTLS: TlsTxSw {before:?} -> {after:?}");
    if std::env::var_os("VERILITH_REQUIRE_KTLS").is_some() {
        assert!(matches!((before, after), (Some(a), Some(b)) if b >= a + 3), "the kernel sealed for no connection: TlsTxSw {before:?} -> {after:?}");
    }
}

#[test]
fn ktls_key_update() {
    let mut s = connect(None, b"http/1.1");
    get(&mut s, "/plaintext", false);
    get(&mut s, "/mid", false);
    for _ in 0..3 {
        // KeyUpdate with update_requested: the server must answer under
        // its old keys, then send under new ones.
        s.conn.refresh_traffic_keys().unwrap();
        get(&mut s, "/mid", false);
        get(&mut s, "/huge", false);
    }
    get(&mut s, "/plaintext", true);
    ends_cleanly(&mut s);
}

#[test]
fn ktls_h2() {
    let mut s = connect(None, b"h2");
    let mut req = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".to_vec();
    req.extend_from_slice(&[0, 0, 0, 4, 0, 0, 0, 0, 0]);
    s.write_all(&req).unwrap();
    s.flush().unwrap();
    let mut frame = |s: &mut Stream| {
        let mut h = [0u8; 9];
        s.read_exact(&mut h).unwrap();
        let mut p = vec![0u8; (h[0] as usize) << 16 | (h[1] as usize) << 8 | h[2] as usize];
        s.read_exact(&mut p).unwrap();
        (h[3], h[4], p)
    };
    // Its SETTINGS, then frames until the ACK of ours.
    assert_eq!(frame(&mut s).0, 4);
    std::thread::sleep(Duration::from_millis(50));
    // PINGs, answered after kTLS took over.
    for i in 0..3u8 {
        let mut ping = vec![0, 0, 8, 6, 0, 0, 0, 0, 0];
        ping.extend_from_slice(&[i; 8]);
        s.write_all(&ping).unwrap();
        s.flush().unwrap();
        loop {
            let (t, fl, p) = frame(&mut s);
            if t == 6 {
                assert_eq!((fl, p), (1, vec![i; 8]));
                break;
            }
        }
    }
}
