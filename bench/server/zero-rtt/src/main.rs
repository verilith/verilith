// Time to first response byte through a proxy that delays each direction
// by RTT/2: full handshake, resumption, resumption with 0-RTT.
use rustls::pki_types::{CertificateDer, ServerName, pem::PemObject};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::{Duration, Instant};

fn pipe(mut a: TcpStream, mut b: TcpStream, half: Duration) {
    let (tx, rx) = std::sync::mpsc::channel::<(Instant, Vec<u8>)>();
    std::thread::spawn(move || {
        for (t, d) in rx {
            let now = Instant::now();
            if t + half > now { std::thread::sleep(t + half - now); }
            if b.write_all(&d).is_err() { return; }
        }
    });
    let mut buf = vec![0u8; 65536];
    loop {
        match a.read(&mut buf) {
            Ok(0) | Err(_) => return,
            Ok(n) => { let _ = tx.send((Instant::now(), buf[..n].to_vec())); }
        }
    }
}

fn proxy(listen: u16, to: u16, half: Duration) {
    let l = TcpListener::bind(("127.0.0.1", listen)).unwrap();
    std::thread::spawn(move || for c in l.incoming() {
        let c = c.unwrap();
        c.set_nodelay(true).unwrap();
        let s = TcpStream::connect(("127.0.0.1", to)).unwrap();
        s.set_nodelay(true).unwrap();
        let (c2, s2) = (c.try_clone().unwrap(), s.try_clone().unwrap());
        std::thread::spawn(move || pipe(c, s, half));
        std::thread::spawn(move || pipe(s2, c2, half));
    });
}

fn once(cc: &Arc<rustls::ClientConfig>, port: u16) -> (Duration, bool, bool) {
    let req = b"GET /plaintext HTTP/1.1\r\nHost: x\r\n\r\n";
    let mut sock = TcpStream::connect(("127.0.0.1", port)).unwrap();
    sock.set_nodelay(true).unwrap();
    let t = Instant::now();
    let mut c = rustls::ClientConnection::new(cc.clone(), ServerName::try_from("localhost").unwrap()).unwrap();
    let early = match c.early_data() { Some(mut e) => { e.write_all(req).unwrap(); true } None => false };
    if !early { c.writer().write_all(req).unwrap(); }
    let mut got = Vec::new();
    let mut s = rustls::Stream::new(&mut c, &mut sock);
    let mut b = [0u8; 4096];
    while !got.windows(13).any(|w| w == b"Hello, World!") {
        let n = s.read(&mut b).unwrap();
        got.extend_from_slice(&b[..n]);
    }
    let d = t.elapsed();
    let resumed = c.handshake_kind() == Some(rustls::HandshakeKind::Resumed);
    let acc = c.is_early_data_accepted();
    (d, resumed, acc)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (port, cert, rtt_ms): (u16, &str, u64) = (a[1].parse().unwrap(), &a[2], a[3].parse().unwrap());
    proxy(port + 1000, port, Duration::from_micros(rtt_ms * 500));
    let mut roots = rustls::RootCertStore::empty();
    for c in CertificateDer::pem_file_iter(cert).unwrap() { roots.add(c.unwrap()).unwrap(); }
    let mk = |early: bool| {
        let mut c = rustls::ClientConfig::builder().with_root_certificates(roots.clone()).with_no_client_auth();
        c.alpn_protocols = vec![b"http/1.1".to_vec()];
        c.enable_early_data = early;
        Arc::new(c)
    };
    for (name, early, fresh) in [("full", false, true), ("resumed", false, false), ("resumed+0rtt", true, false)] {
        let mut v = Vec::new();
        for _ in 0..20 {
            let cc = mk(early);
            if !fresh { once(&cc, port + 1000); }
            let (d, r, acc) = once(&cc, port + 1000);
            assert_eq!(r, !fresh, "{name}");
            if early { assert!(acc, "0-RTT accepted"); }
            v.push(d.as_secs_f64() * 1000.0);
        }
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!("{name:14} median {:6.1} ms  (RTT {rtt_ms} ms, TCP connect to the proxy not counted)", v[v.len() / 2]);
    }
}
