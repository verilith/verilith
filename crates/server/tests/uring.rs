//! The io_uring event loop against the epoll one: the same requests over
//! real sockets give byte-identical responses (Linux only).
#![cfg(target_os = "linux")]
use std::io::{Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use verilith_server::h1::StaticBody;
use verilith_server::{serve, Config, Fields, Request, Response};

fn bodies() -> &'static (Vec<u8>, StaticBody, StaticBody) {
    static B: OnceLock<(Vec<u8>, StaticBody, StaticBody)> = OnceLock::new();
    B.get_or_init(|| {
        let big: Vec<u8> = (0..300_000u32).map(|i| (i * 7 + i / 251) as u8).collect();
        // 64 KiB: sendfile from a sealed memfd; 1 MiB: writev from memory.
        let mid = StaticBody::new(big[..65536].to_vec());
        let huge = StaticBody::new((0..1 << 20).map(|i: u32| (i % 253) as u8).collect());
        (big, mid, huge)
    })
}

fn handler(req: &Request, res: &mut Response) {
    let f = Fields::new(&[]).unwrap();
    let (big, mid, huge) = bodies();
    let _ = match req.path() {
        b"/plaintext" => res.send_prepared(200, &f, b"Hello, World!"),
        b"/big" => res.send_prepared(200, &f, big),
        b"/mid" => res.send_static(200, &f, mid),
        b"/huge" => res.send_static(200, &f, huge),
        _ => {
            res.error(404);
            Ok(())
        }
    };
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

/// The HTTP/1.1 port of a server on each loop: (epoll, io_uring).
fn servers() -> (u16, u16) {
    static P: OnceLock<(u16, u16)> = OnceLock::new();
    *P.get_or_init(|| {
        let mut ports = [0u16; 2];
        for (i, uring) in [false, true].into_iter().enumerate() {
            let port = free_port();
            ports[i] = port;
            let cfg = Config { port, threads: 2, pin: false, io_uring: uring, ..Config::default() };
            std::thread::spawn(move || serve(cfg, Arc::new(handler)));
        }
        for p in ports {
            for _ in 0..200 {
                if TcpStream::connect(("127.0.0.1", p)).is_ok() {
                    break;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
        (ports[0], ports[1])
    })
}

/// Sends `req` (in pieces of `chunk` bytes), half-closes, reads to EOF,
/// and blanks the Date value so two servers' replies compare.
fn exchange(port: u16, req: &[u8], chunk: usize) -> Vec<u8> {
    let mut s = TcpStream::connect(("127.0.0.1", port)).unwrap();
    s.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
    for c in req.chunks(chunk.max(1)) {
        s.write_all(c).unwrap();
        if chunk < req.len() {
            std::thread::sleep(Duration::from_millis(1));
        }
    }
    s.shutdown(Shutdown::Write).unwrap();
    let mut out = Vec::new();
    s.read_to_end(&mut out).unwrap();
    blank_dates(&mut out);
    out
}

fn blank_dates(b: &mut [u8]) {
    let k = b"\r\nDate: ";
    let mut i = 0;
    while i + k.len() + 29 <= b.len() {
        if &b[i..i + k.len()] == k {
            for x in &mut b[i + k.len()..i + k.len() + 29] {
                *x = b'x';
            }
        }
        i += 1;
    }
}

fn same(req: &[u8], chunk: usize) -> Vec<u8> {
    let (e, u) = servers();
    let a = exchange(e, req, chunk);
    let b = exchange(u, req, chunk);
    if a != b {
        let d = a.iter().zip(&b).position(|(x, y)| x != y).unwrap_or(a.len().min(b.len()));
        panic!("epoll and io_uring differ (lengths {} and {}, first at {d}): {:?} / {:?}", a.len(), b.len(), String::from_utf8_lossy(&a[d.saturating_sub(40)..(d + 40).min(a.len())]), String::from_utf8_lossy(&b[d.saturating_sub(40)..(d + 40).min(b.len())]));
    }
    a
}

#[test]
fn one_request() {
    let r = same(b"GET /plaintext HTTP/1.1\r\nHost: x\r\n\r\n", usize::MAX);
    assert!(r.starts_with(b"HTTP/1.1 200") && r.ends_with(b"Hello, World!"));
}

#[test]
fn pipelined_and_large() {
    let mut req = Vec::new();
    for p in ["/plaintext", "/big", "/mid", "/nope", "/huge", "/plaintext"].iter().cycle().take(60) {
        req.extend_from_slice(format!("GET {p} HTTP/1.1\r\nHost: x\r\n\r\n").as_bytes());
    }
    let r = same(&req, usize::MAX);
    let (big, _, huge) = bodies();
    assert!(r.len() > 10 * (big.len() + huge.bytes().len()));
    // Split anywhere: the same bytes.
    let r2 = same(&req[..req.len() / 4], 37);
    assert!(!r2.is_empty());
}

#[test]
fn many_connections_at_once() {
    let (_, u) = servers();
    let ts: Vec<_> = (0..64)
        .map(|i| {
            std::thread::spawn(move || {
                let path = if i % 3 == 0 { "/mid" } else { "/plaintext" };
                let req = format!("GET {path} HTTP/1.1\r\nHost: x\r\n\r\n").repeat(20);
                let r = exchange(u, req.as_bytes(), usize::MAX);
                assert_eq!(r.windows(12).filter(|w| w == b"HTTP/1.1 200").count(), 20);
            })
        })
        .collect();
    for t in ts {
        t.join().unwrap();
    }
}

#[test]
fn reset_mid_response_leaves_the_server_serving() {
    let (_, u) = servers();
    for _ in 0..20 {
        let mut s = TcpStream::connect(("127.0.0.1", u)).unwrap();
        s.write_all(&b"GET /huge HTTP/1.1\r\nHost: x\r\n\r\n".repeat(8)).unwrap();
        drop(s); // closed with the responses unread
    }
    let r = exchange(u, b"GET /plaintext HTTP/1.1\r\nHost: x\r\n\r\n", usize::MAX);
    assert!(r.ends_with(b"Hello, World!"));
}
