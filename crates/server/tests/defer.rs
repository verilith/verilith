//! Deferred responses (`Response::defer`) and the worker's reactor
//! (`register`, `Handler::on_io`), over a real socket: answered later from
//! another thread, from the worker itself on a socket event, or dropped.
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use verilith_server::{serve, Config, Field, Handler, Pending, Request, Response};

struct H;

thread_local! {
    /// `/io` requests waiting on a pipe, by the pipe's read end.
    static WAITING: RefCell<HashMap<u64, (i32, Pending)>> = RefCell::new(HashMap::new());
}

fn pipe() -> (i32, i32) {
    let mut fds = [0i32; 2];
    unsafe extern "C" {
        fn pipe(fds: *mut i32) -> i32;
    }
    assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0);
    (fds[0], fds[1])
}

impl Handler for H {
    fn handle(&self, req: &Request, res: &mut Response) {
        let path = req.path().to_vec();
        match &path[..] {
            b"/now" => {
                let _ = res.send(200, &[], b"now");
            }
            b"/later" => {
                let ms: u64 = std::str::from_utf8(&req.target[b"/later?".len().min(req.target.len())..]).ok().and_then(|s| s.parse().ok()).unwrap_or(20);
                let body = req.body.to_vec();
                let p = res.defer().expect("deferral on an epoll worker");
                std::thread::spawn(move || {
                    std::thread::sleep(Duration::from_millis(ms));
                    p.complete(move |res| {
                        let mut b = format!("later {ms} ").into_bytes();
                        b.extend_from_slice(&body);
                        let _ = res.send(200, &[Field { name: b"X-Deferred", value: b"1" }], &b);
                    });
                });
            }
            b"/drop" => {
                drop(res.defer());
            }
            b"/silent" => {
                // Completed with a function that sends nothing: 502.
                let p = res.defer().unwrap();
                p.complete(|_| {});
            }
            b"/io" => {
                // Answered on the worker, when a pipe another thread writes
                // to turns readable.
                let (r, w) = pipe();
                let p = res.defer().unwrap();
                verilith_server::register(r, r as u64).unwrap();
                WAITING.with(|m| m.borrow_mut().insert(r as u64, (r, p)));
                std::thread::spawn(move || {
                    std::thread::sleep(Duration::from_millis(10));
                    unsafe extern "C" {
                        fn write(fd: i32, b: *const u8, n: usize) -> isize;
                        fn close(fd: i32) -> i32;
                    }
                    unsafe {
                        write(w, b"x".as_ptr(), 1);
                        close(w);
                    }
                });
            }
            _ => res.error(404),
        }
    }

    fn on_io(&self, token: u64, readable: bool, _writable: bool) {
        if !readable {
            return;
        }
        if let Some((fd, p)) = WAITING.with(|m| m.borrow_mut().remove(&token)) {
            unsafe extern "C" {
                fn close(fd: i32) -> i32;
            }
            unsafe { close(fd) };
            p.complete(|res| {
                let _ = res.send(200, &[], b"io");
            });
        }
    }
}

fn port() -> u16 {
    static P: OnceLock<u16> = OnceLock::new();
    *P.get_or_init(|| {
        let port = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let h2c = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        H2C.set(h2c).unwrap();
        let cfg = Config { port, h2c_port: Some(h2c), threads: 2, pin: false, ..Config::default() };
        std::thread::spawn(move || serve(cfg, Arc::new(H)).unwrap());
        for _ in 0..100 {
            if TcpStream::connect(("127.0.0.1", port)).is_ok() {
                break;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        port
    })
}

static H2C: OnceLock<u16> = OnceLock::new();

/// Sends `reqs` back to back on one connection and reads `n` responses:
/// (status, body) each, parsed by verilith-http.
fn pipeline(reqs: &[u8], n: usize) -> Vec<(u16, Vec<u8>)> {
    let mut s = TcpStream::connect(("127.0.0.1", port())).unwrap();
    s.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    s.write_all(reqs).unwrap();
    let mut buf = Vec::new();
    let mut out = Vec::new();
    while out.len() < n {
        let mut hs = Vec::new();
        match verilith_http::parse_response(&buf, false, false, &mut hs) {
            Ok(verilith_http::Status::Complete(r)) => {
                let len = r.head_len;
                let cl = match r.body {
                    verilith_http::Body::Length(n) => n as usize,
                    verilith_http::Body::Empty => 0,
                    b => panic!("framing {b:?}"),
                };
                if buf.len() >= len + cl {
                    out.push((r.status(), buf[len..len + cl].to_vec()));
                    buf.drain(..len + cl);
                    continue;
                }
            }
            Ok(verilith_http::Status::Partial) => {}
            Err(e) => panic!("bad response: {e:?}"),
        }
        let mut b = [0u8; 4096];
        let k = s.read(&mut b).unwrap();
        assert!(k > 0, "connection closed after {} responses", out.len());
        buf.extend_from_slice(&b[..k]);
    }
    out
}

#[test]
fn http11_deferred_in_order() {
    // The first answer comes last, yet responses keep request order.
    let reqs = b"GET /later?60 HTTP/1.1\r\nHost: a\r\n\r\nGET /now HTTP/1.1\r\nHost: a\r\n\r\nPOST /later?5 HTTP/1.1\r\nHost: a\r\nContent-Length: 3\r\n\r\nabcGET /io HTTP/1.1\r\nHost: a\r\n\r\nGET /now HTTP/1.1\r\nHost: a\r\n\r\n";
    let r = pipeline(reqs, 5);
    assert_eq!(r[0], (200, b"later 60 ".to_vec()));
    assert_eq!(r[1], (200, b"now".to_vec()));
    assert_eq!(r[2], (200, b"later 5 abc".to_vec()));
    assert_eq!(r[3], (200, b"io".to_vec()));
    assert_eq!(r[4], (200, b"now".to_vec()));
}

#[test]
fn http11_dropped_and_silent_are_502() {
    let reqs = b"GET /drop HTTP/1.1\r\nHost: a\r\n\r\nGET /silent HTTP/1.1\r\nHost: a\r\n\r\nGET /now HTTP/1.1\r\nHost: a\r\n\r\n";
    let r = pipeline(reqs, 3);
    assert_eq!(r[0].0, 502);
    assert_eq!(r[1].0, 502);
    assert_eq!(r[2], (200, b"now".to_vec()));
}

#[test]
fn http11_client_gone_before_answer() {
    // The connection closes while its answer is pending; the server keeps
    // serving (the completion finds the slot reused or empty).
    for _ in 0..20 {
        let mut s = TcpStream::connect(("127.0.0.1", port())).unwrap();
        s.write_all(b"GET /later?30 HTTP/1.1\r\nHost: a\r\n\r\n").unwrap();
        drop(s);
    }
    std::thread::sleep(Duration::from_millis(60));
    let r = pipeline(b"GET /now HTTP/1.1\r\nHost: a\r\n\r\n", 1);
    assert_eq!(r[0], (200, b"now".to_vec()));
}

fn curl(args: &[&str]) -> Option<String> {
    let o = std::process::Command::new("curl").args(args).output().ok()?;
    if !o.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&o.stdout).into_owned())
}

#[test]
fn h2c_deferred_streams() {
    let _ = port();
    let h2c = *H2C.get().unwrap();
    let base = format!("http://127.0.0.1:{h2c}");
    // Several streams on one connection: curl multiplexes them.
    let urls: Vec<String> = ["/later?80", "/now", "/io", "/later?1", "/drop"].iter().map(|p| format!("{base}{p}")).collect();
    let mut args = vec!["-s", "--http2-prior-knowledge", "-w", "[%{http_code}]\n"];
    for u in &urls {
        args.push(u);
    }
    let Some(out) = curl(&args) else {
        eprintln!("skipped: no curl with HTTP/2");
        return;
    };
    assert_eq!(out, "later 80 [200]\nnow[200]\nio[200]\nlater 1 [200]\nBad Gateway[502]\n");
}

/// The same over TLS: HTTP/1.1 and h2 by ALPN.
#[cfg(feature = "tls")]
#[test]
fn tls_deferred() {
    let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
    let tcfg = verilith_server::tls::config_der(vec![c.cert.der().to_vec()], &c.signing_key.serialize_der()).unwrap();
    let port = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
    let tls = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
    let cfg = Config { port, tls: Some((tls, tcfg)), threads: 1, pin: false, ..Config::default() };
    std::thread::spawn(move || serve(cfg, Arc::new(H)).unwrap());
    for _ in 0..100 {
        if TcpStream::connect(("127.0.0.1", tls)).is_ok() {
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let base = format!("https://127.0.0.1:{tls}");
    let urls: Vec<String> = ["/later?50", "/now", "/io", "/drop"].iter().map(|p| format!("{base}{p}")).collect();
    for v in ["--http1.1", "--http2"] {
        let mut args = vec!["-sk", v, "-w", "[%{http_code}]\n"];
        for u in &urls {
            args.push(u);
        }
        let Some(out) = curl(&args) else {
            eprintln!("skipped: no curl");
            return;
        };
        assert_eq!(out, "later 50 [200]\nnow[200]\nio[200]\nBad Gateway[502]\n", "{v}");
    }
}
