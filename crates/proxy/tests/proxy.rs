//! The proxy end to end: a scripted HTTP/1.1 upstream on real sockets,
//! the proxy in front of it on verilith-server, and clients over
//! HTTP/1.1, h2c and (with `--features tls`) HTTPS.
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use verilith_proxy::proxy::{Config as ProxyConfig, Proxy, Server};
use verilith_proxy::route::Route;
use verilith_server::{serve, Config};

// ---- The upstream ----------------------------------------------------------

static HITS: AtomicUsize = AtomicUsize::new(0);
static CONNS: AtomicUsize = AtomicUsize::new(0);

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

/// An upstream whose answers are scripted by path; `tag` is put in every
/// response so tests can tell upstreams apart.
fn upstream(tag: &'static str) -> u16 {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = l.local_addr().unwrap().port();
    std::thread::spawn(move || {
        for s in l.incoming() {
            let Ok(s) = s else { continue };
            let id = CONNS.fetch_add(1, Ordering::SeqCst);
            std::thread::spawn(move || conn(s, id, tag));
        }
    });
    port
}

fn conn(s: TcpStream, id: usize, tag: &str) {
    let mut w = s.try_clone().unwrap();
    let mut r = BufReader::new(s);
    loop {
        let mut head = Vec::new();
        loop {
            let mut line = Vec::new();
            if r.read_until(b'\n', &mut line).unwrap_or(0) == 0 {
                return;
            }
            head.extend_from_slice(&line);
            if line == b"\r\n" {
                break;
            }
        }
        let text = String::from_utf8_lossy(&head).to_string();
        let target = text.split(' ').nth(1).unwrap_or("").to_string();
        let cl: usize = text
            .lines()
            .find_map(|l| l.to_ascii_lowercase().strip_prefix("content-length:").map(|v| v.trim().parse().unwrap()))
            .unwrap_or(0);
        let mut body = vec![0; cl];
        r.read_exact(&mut body).unwrap();
        let path = target.split('?').next().unwrap().to_string();
        let ok = |w: &mut TcpStream, extra: &str, b: &[u8]| {
            let h = format!("HTTP/1.1 200 OK\r\nX-Up: {tag}\r\n{extra}Content-Length: {}\r\n\r\n", b.len());
            w.write_all(h.as_bytes()).and_then(|_| w.write_all(b))
        };
        let res = match &path[..] {
            "/echo" => {
                let mut b = head.clone();
                b.extend_from_slice(&body);
                ok(&mut w, "Content-Type: text/plain\r\nConnection: x-hop\r\nX-Hop: gone\r\nKeep-Alive: timeout=5\r\n", &b)
            }
            "/conn" => ok(&mut w, "", id.to_string().as_bytes()),
            "/chunked" => w.write_all(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n1;ext=1\r\n \r\n5\r\nworld\r\n0\r\nX-Trailer: t\r\n\r\n"),
            "/close" => {
                let _ = w.write_all(b"HTTP/1.1 200 OK\r\nConnection: close\r\n\r\nuntil the end");
                return;
            }
            "/interim" => w.write_all(b"HTTP/1.1 103 Early Hints\r\nLink: </a>; rel=preload\r\n\r\nHTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nfinal"),
            "/cache" => {
                let n = HITS.fetch_add(1, Ordering::SeqCst);
                ok(&mut w, "Cache-Control: max-age=60\r\nAge: 5\r\n", format!("n={n}").as_bytes())
            }
            "/short" => {
                let n = HITS.fetch_add(1, Ordering::SeqCst);
                ok(&mut w, "Cache-Control: max-age=1\r\n", format!("n={n}").as_bytes())
            }
            "/nostore" => {
                let n = HITS.fetch_add(1, Ordering::SeqCst);
                ok(&mut w, "Cache-Control: no-store, max-age=60\r\n", format!("n={n}").as_bytes())
            }
            "/cookie" => {
                let n = HITS.fetch_add(1, Ordering::SeqCst);
                ok(&mut w, "Cache-Control: max-age=60\r\nSet-Cookie: a=b\r\n", format!("n={n}").as_bytes())
            }
            "/html" => ok(&mut w, "Content-Type: text/html\r\nETag: \"v1\"\r\nCache-Control: max-age=60\r\n", &html()),
            "/png" => ok(&mut w, "Content-Type: image/png\r\n", &html()),
            "/poison" => {
                // A response, then bytes nobody asked for: a second
                // response that must never reach another client.
                w.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nsafeHTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nEVIL!")
            }
            "/late" => {
                let w2 = w.try_clone().unwrap();
                std::thread::spawn(move || {
                    std::thread::sleep(Duration::from_millis(100));
                    let mut w2 = w2;
                    let _ = w2.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nEVIL!");
                });
                ok(&mut w, "", b"late")
            }
            "/slow" => {
                std::thread::sleep(Duration::from_millis(1500));
                ok(&mut w, "", b"slow")
            }
            "/hangup" => return,
            "/garbage" => w.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 1\r\nContent-Length: 2\r\n\r\nab"),
            "/upgrade" => w.write_all(b"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: upgrade\r\n\r\n"),
            "/big" => ok(&mut w, "", &vec![b'x'; 300_000]),
            _ => ok(&mut w, "", format!("{tag} {path}").as_bytes()),
        };
        if res.is_err() {
            return;
        }
    }
}

fn html() -> Vec<u8> {
    let mut b = Vec::new();
    for i in 0..400 {
        b.extend_from_slice(format!("<p>paragraph {i} of a page the proxy compresses</p>\n").as_bytes());
    }
    b
}

// ---- The proxy -------------------------------------------------------------

struct Ports {
    http: u16,
    h2c: u16,
    #[cfg(feature = "tls")]
    tls: u16,
}

fn proxy() -> &'static Ports {
    static P: OnceLock<Ports> = OnceLock::new();
    P.get_or_init(|| {
        let a = upstream("a");
        let b = upstream("b");
        let dead = free_port();
        let s = |port| Server { addr: [127, 0, 0, 1], port };
        let pc = ProxyConfig {
            upstreams: vec![vec![s(a)], vec![s(b)], vec![s(dead)], vec![s(dead), s(a)]],
            routes: vec![
                Route { host: None, prefix: vec![], upstream: 0 },
                Route { host: None, prefix: vec![b"api".to_vec()], upstream: 1 },
                Route { host: Some(b"B.example".to_vec()), prefix: vec![], upstream: 1 },
                Route { host: None, prefix: vec![b"dead".to_vec()], upstream: 2 },
                Route { host: None, prefix: vec![b"half".to_vec()], upstream: 3 },
            ],
            response_timeout: Duration::from_millis(700),
            max_response: 200_000,
            ..ProxyConfig::default()
        };
        let ports = Ports {
            http: free_port(),
            h2c: free_port(),
            #[cfg(feature = "tls")]
            tls: free_port(),
        };
        #[cfg(feature = "tls")]
        let tcfg = {
            let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
            verilith_server::tls::config_der(vec![c.cert.der().to_vec()], &c.signing_key.serialize_der()).unwrap()
        };
        let cfg = Config {
            port: ports.http,
            h2c_port: Some(ports.h2c),
            threads: 2,
            pin: false,
            server: b"verilith-proxy",
            #[cfg(feature = "tls")]
            tls: Some((ports.tls, tcfg)),
            ..Config::default()
        };
        std::thread::spawn(move || serve(cfg, Arc::new(Proxy::new(pc))).unwrap());
        for _ in 0..100 {
            if TcpStream::connect(("127.0.0.1", ports.http)).is_ok() {
                break;
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        ports
    })
}

// ---- Clients ---------------------------------------------------------------

struct Got {
    status: u16,
    fields: Vec<(String, String)>,
    body: Vec<u8>,
}

impl Got {
    fn field(&self, n: &str) -> Option<&str> {
        self.fields.iter().find(|(k, _)| k.eq_ignore_ascii_case(n)).map(|(_, v)| &v[..])
    }
    fn text(&self) -> String {
        String::from_utf8_lossy(&self.body).to_string()
    }
}

/// One HTTP/1.1 connection to the proxy.
struct H1(TcpStream, Vec<u8>);

impl H1 {
    fn new() -> H1 {
        let s = TcpStream::connect(("127.0.0.1", proxy().http)).unwrap();
        s.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        H1(s, Vec::new())
    }

    fn send(&mut self, method: &str, target: &str, extra: &[(&str, &str)], body: &[u8]) -> Got {
        let mut r = format!("{method} {target} HTTP/1.1\r\nHost: localhost\r\n");
        for (k, v) in extra {
            r.push_str(&format!("{k}: {v}\r\n"));
        }
        if !body.is_empty() {
            r.push_str(&format!("Content-Length: {}\r\n", body.len()));
        }
        r.push_str("\r\n");
        self.0.write_all(r.as_bytes()).unwrap();
        self.0.write_all(body).unwrap();
        self.read(method == "HEAD")
    }

    fn get(&mut self, target: &str) -> Got {
        self.send("GET", target, &[], b"")
    }

    fn read(&mut self, head: bool) -> Got {
        loop {
            let mut hs = Vec::new();
            if let Ok(verilith_http::Status::Complete(r)) = verilith_http::parse_response(&self.1, head, false, &mut hs) {
                let len = r.head_len;
                let cl = match r.body {
                    verilith_http::Body::Length(n) => n as usize,
                    verilith_http::Body::Empty => 0,
                    b => panic!("framing {b:?}"),
                };
                if self.1.len() >= len + cl {
                    let fields = r.headers(&hs).map(|(n, v)| (String::from_utf8_lossy(n).to_string(), String::from_utf8_lossy(v).to_string())).collect();
                    let g = Got { status: r.status(), fields, body: self.1[len..len + cl].to_vec() };
                    self.1.drain(..len + cl);
                    return g;
                }
            }
            let mut b = [0u8; 65536];
            let n = self.0.read(&mut b).expect("a response");
            assert!(n > 0, "the proxy closed the connection");
            self.1.extend_from_slice(&b[..n]);
        }
    }
}

fn get(target: &str) -> Got {
    H1::new().get(target)
}

fn curl(args: &[&str]) -> Option<String> {
    let out = std::process::Command::new("curl").args(args).output().ok()?;
    Some(String::from_utf8_lossy(&out.stdout).to_string())
}

// ---- Tests -----------------------------------------------------------------

#[test]
fn forwards_and_filters_fields() {
    let g = H1::new().send(
        "POST",
        "/echo?q=1",
        &[("Connection", "x-private, keep-alive"), ("X-Private", "secret"), ("TE", "trailers"), ("X-Forwarded-For", "6.6.6.6"), ("Cookie", "a=1"), ("Cookie", "b=2"), ("X-Kept", "yes")],
        b"the body",
    );
    assert_eq!(g.status, 200);
    let up = g.text();
    // What the upstream read.
    assert!(up.starts_with("POST /echo?q=1 HTTP/1.1\r\nHost: localhost\r\n"), "{up}");
    assert!(up.contains("X-Kept: yes\r\n"), "{up}");
    assert!(up.contains("Cookie: a=1; b=2\r\n"), "{up}");
    assert!(up.contains("X-Forwarded-For: 127.0.0.1\r\n"), "{up}");
    assert!(up.contains("X-Forwarded-Proto: http\r\n"), "{up}");
    assert!(up.contains("Via: 1.1 verilith\r\n"), "{up}");
    assert!(up.contains("Content-Length: 8\r\n"), "{up}");
    assert!(up.ends_with("\r\n\r\nthe body"), "{up}");
    for gone in ["x-private", "6.6.6.6", "TE:", "keep-alive"] {
        assert!(!up.to_ascii_lowercase().contains(&gone.to_ascii_lowercase()), "{gone} forwarded: {up}");
    }
    // What the client read: the upstream's hop-by-hop fields removed.
    assert_eq!(g.field("x-up"), Some("a"));
    assert_eq!(g.field("x-hop"), None);
    assert_eq!(g.field("keep-alive"), None);
    assert_eq!(g.field("server"), Some("verilith-proxy"));
}

#[test]
fn routes_by_resolved_path_and_host() {
    assert_eq!(get("/x").text(), "a /x");
    assert_eq!(get("/api/v1").text(), "b /api/v1");
    assert_eq!(get("/api").text(), "b /api");
    // Component prefixes: /apix is not under /api.
    assert_eq!(get("/apix").text(), "a /apix");
    // The router sees the resolved path; the upstream gets it as sent.
    assert_eq!(get("/%61pi/x").text(), "b /%61pi/x");
    assert_eq!(get("/api/../x").text(), "a /api/../x");
    assert_eq!(get("/x/../api/y").text(), "b /x/../api/y");
    // Escapes above the root, and encoded slashes, are refused.
    assert_eq!(get("/../x").status, 400);
    assert_eq!(get("/api%2fx").status, 400);
    // A route for a host, case-insensitively, with its port ignored.
    let g = H1::new().send("GET", "/x", &[], b"");
    assert_eq!(g.text(), "a /x");
    let mut c = H1::new();
    c.0.write_all(b"GET /x HTTP/1.1\r\nHost: b.EXAMPLE:8080\r\n\r\n").unwrap();
    assert_eq!(c.read(false).text(), "b /x");
}

#[test]
fn reuses_upstream_connections() {
    let mut c = H1::new();
    let first = c.get("/conn").text();
    for _ in 0..5 {
        assert_eq!(c.get("/conn").text(), first);
    }
}

#[test]
fn chunked_close_delimited_and_interim() {
    let g = get("/chunked");
    assert_eq!((g.status, g.text().as_str()), (200, "hello world"));
    assert_eq!(g.field("transfer-encoding"), None);
    let g = get("/close");
    assert_eq!((g.status, g.text().as_str()), (200, "until the end"));
    let g = get("/interim");
    assert_eq!((g.status, g.text().as_str()), (200, "final"));
    // The proxy's own framing, whatever the upstream's.
    assert_eq!(g.field("content-length"), Some("5"));
}

#[test]
fn never_reuses_a_desynchronized_connection() {
    let mut c = H1::new();
    assert_eq!(c.get("/poison").text(), "safe");
    for _ in 0..10 {
        let g = c.get("/conn");
        assert_ne!(g.text(), "EVIL!");
        assert_eq!(g.status, 200);
    }
    // Bytes arriving on an idle connection close it.
    assert_eq!(c.get("/late").text(), "late");
    std::thread::sleep(Duration::from_millis(300));
    for _ in 0..10 {
        assert_ne!(c.get("/conn").text(), "EVIL!");
    }
}

#[test]
fn bad_upstreams() {
    assert_eq!(get("/garbage").status, 502);
    assert_eq!(get("/upgrade").status, 502);
    assert_eq!(get("/hangup").status, 502);
    assert_eq!(get("/big").status, 502);
    assert_eq!(get("/dead/x").status, 502);
    // One server of two down: the other answers.
    for _ in 0..4 {
        assert_eq!(get("/half/x").text(), "a /half/x");
    }
    let t = std::time::Instant::now();
    assert_eq!(get("/slow").status, 504);
    assert!(t.elapsed() < Duration::from_millis(1400));
    // The connection the slow response was on is not reused.
    std::thread::sleep(Duration::from_millis(1000));
    assert_eq!(get("/x").text(), "a /x");
}

#[test]
fn caches_what_the_rules_allow() {
    let n = |g: Got| g.text();
    let a = n(get("/cache?1"));
    let g = get("/cache?1");
    assert_eq!(g.text(), a, "served from the cache");
    let age: u64 = g.field("age").unwrap().parse().unwrap();
    assert!((5..7).contains(&age), "age {age}");
    assert_ne!(n(get("/cache?2")), a, "the query is part of the key");
    // Asked not to use a stored response.
    let b = n(H1::new().send("GET", "/cache?1", &[("Cache-Control", "no-cache")], b""));
    assert_ne!(b, a);
    for p in ["/nostore", "/cookie"] {
        let x = n(get(p));
        assert_ne!(n(get(p)), x, "{p} cached");
    }
    // Expired.
    let x = n(get("/short"));
    assert_eq!(n(get("/short")), x);
    std::thread::sleep(Duration::from_millis(2100));
    assert_ne!(n(get("/short")), x);
    // POST is never answered from the cache.
    let p = H1::new().send("POST", "/cache?1", &[], b"x");
    assert_ne!(p.text(), b);
    // HEAD: the length of the body GET would send.
    let h = H1::new().send("HEAD", "/cache?3", &[], b"");
    let g = get("/cache?3");
    assert_eq!(h.field("content-length").unwrap(), g.body.len().to_string());
}

#[test]
fn compresses_with_verified_codecs() {
    let page = html();
    for (accept, coding) in [("br", Some("br")), ("gzip, zstd;q=0.9", Some("gzip")), ("zstd", Some("zstd")), ("identity", None), ("br;q=0", None)] {
        let g = H1::new().send("GET", "/html", &[("Accept-Encoding", accept)], b"");
        assert_eq!(g.status, 200);
        assert_eq!(g.field("content-encoding"), coding, "{accept}");
        assert_eq!(g.field("vary"), Some("Accept-Encoding"));
        let body = match coding {
            Some("br") => verilith_brotli::decompress(&g.body, 1 << 20).unwrap(),
            Some("zstd") => verilith_zstd::decompress(&g.body, 1 << 20).unwrap(),
            Some("gzip") => verilith_zlib::gzip_decompress(&g.body).unwrap(),
            _ => g.body.clone(),
        };
        assert_eq!(body, page, "{accept}");
        if coding.is_some() {
            assert!(g.body.len() < page.len() / 4);
            assert_eq!(g.field("etag"), Some("W/\"v1\""));
        } else {
            assert_eq!(g.field("etag"), Some("\"v1\""));
        }
    }
    // Not a compressible type.
    let g = H1::new().send("GET", "/png", &[("Accept-Encoding", "br")], b"");
    assert_eq!(g.field("content-encoding"), None);
}

#[test]
fn h2c_and_concurrency() {
    let base = format!("http://127.0.0.1:{}", proxy().h2c);
    let urls: Vec<String> = ["/x", "/api/y", "/chunked", "/dead/z"].iter().map(|p| format!("{base}{p}")).collect();
    let mut args = vec!["-s", "--http2-prior-knowledge", "-w", "[%{http_code}]\n"];
    for u in &urls {
        args.push(u);
    }
    let Some(out) = curl(&args) else {
        eprintln!("skipped: no curl");
        return;
    };
    assert_eq!(out, "a /x[200]\nb /api/y[200]\nhello world[200]\nBad Gateway[502]\n");
    // Many clients at once.
    let ts: Vec<_> = (0..16)
        .map(|i| {
            std::thread::spawn(move || {
                let mut c = H1::new();
                for j in 0..20 {
                    let p = format!("/t{i}-{j}");
                    assert_eq!(c.get(&p).text(), format!("a {p}"));
                }
            })
        })
        .collect();
    for t in ts {
        t.join().unwrap();
    }
}

#[cfg(feature = "tls")]
#[test]
fn https_front() {
    let base = format!("https://127.0.0.1:{}", proxy().tls);
    for v in ["--http1.1", "--http2"] {
        let a = format!("{base}/echo");
        let b = format!("{base}/api/z");
        let Some(out) = curl(&["-sk", v, &a, &b]) else {
            eprintln!("skipped: no curl");
            return;
        };
        assert!(out.contains("X-Forwarded-Proto: https\r\n"), "{v}: {out}");
        assert!(out.ends_with("b /api/z"), "{v}: {out}");
    }
}
