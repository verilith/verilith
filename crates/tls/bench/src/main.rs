//! ClientHello parsing, verilith-tls against rustls, on the same records.
//!
//! The task, both sides: take one TLS record holding a ClientHello, and
//! read the server name, the ALPN protocols, the cipher suites and the
//! signature schemes, summed into a check value. rustls's API for this is
//! `Acceptor` (`read_tls`, `accept`, `client_hello()`), which also checks
//! the record and builds its own copies of the fields; verilith-tls's is
//! `RecordHeader::parse`, `handshake_message_x` and `ClientHello::parse`,
//! which return spans of the input.
//!
//! `tlsbench [ROW]` runs only the named row. `tlsbench --agree` runs the
//! differential check against rustls instead.
use rustls::server::Acceptor;
use std::hint::black_box;
use std::sync::Arc;
use std::time::Instant;
use verilith_tls::hello::ClientHello;
use verilith_tls::record::{RecordHeader, handshake_message_x};

fn bench<F: FnMut() -> usize>(name: &str, msg: &str, mut f: F) {
    if let Some(only) = std::env::args().nth(1) {
        if only != name {
            return;
        }
    }
    for _ in 0..2000 {
        black_box(f());
    }
    let mut samples = Vec::new();
    for _ in 0..31 {
        let iters = 20000;
        let t = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        samples.push(t.elapsed().as_secs_f64() / iters as f64);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{msg}\t{name}\t{:.0}\t{:.0}", samples[15] * 1e9, samples[0] * 1e9);
}

fn record(body: &[u8]) -> Vec<u8> {
    let mut m = vec![1u8, (body.len() >> 16) as u8, (body.len() >> 8) as u8, body.len() as u8];
    m.extend_from_slice(body);
    let mut r = vec![22u8, 3, 1, (m.len() >> 8) as u8, m.len() as u8];
    r.extend_from_slice(&m);
    r
}

fn rustls_hello(alpn: &[&[u8]], sni: &str) -> Vec<u8> {
    let mut cfg = rustls::ClientConfig::builder()
        .with_root_certificates(rustls::RootCertStore::empty())
        .with_no_client_auth();
    cfg.alpn_protocols = alpn.iter().map(|p| p.to_vec()).collect();
    let mut c = rustls::ClientConnection::new(Arc::new(cfg), sni.to_string().try_into().unwrap()).unwrap();
    let mut out = Vec::new();
    c.write_tls(&mut out).unwrap();
    // Strip the record and handshake headers.
    out[9..].to_vec()
}

fn ours(rec: &[u8]) -> usize {
    let h = RecordHeader::parse(rec).unwrap();
    assert!(h.content_type == 22 && h.length == rec.len() - 5);
    let frag = &rec[5..];
    let (t, sp) = handshake_message_x(frag).unwrap();
    assert!(t == 1);
    let b = sp.of(frag);
    let ch = ClientHello::parse(b).unwrap();
    let mut sum = ch.server_name.map_or(0, |s| s.len());
    if let Some(a) = ch.alpn {
        let mut l = a.of(b);
        while let [n, rest @ ..] = l {
            sum += *n as usize;
            l = &rest[*n as usize..];
        }
    }
    sum += ch.cipher_suites.len() / 2;
    sum += ch.signature_algorithms.map_or(0, |s| s.len() / 2);
    sum
}

fn theirs(rec: &[u8]) -> usize {
    let mut acc = Acceptor::default();
    acc.read_tls(&mut &rec[..]).unwrap();
    let a = acc.accept().unwrap().unwrap();
    let ch = a.client_hello();
    let mut sum = ch.server_name().map_or(0, |s| s.len());
    if let Some(it) = ch.alpn() {
        sum += it.map(|p| p.len()).sum::<usize>();
    }
    sum += ch.cipher_suites().len();
    sum += ch.signature_schemes().len();
    sum
}

fn inputs() -> Vec<(String, Vec<u8>)> {
    let mut v = Vec::new();
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/data");
    for name in ["py-default-sni-alpn", "py-tls12-only", "ossl-alpn3", "ossl-p256-p384"] {
        v.push((name.to_string(), std::fs::read(format!("{dir}/{name}.bin")).unwrap()));
    }
    v.push(("rustls-sni-alpn".into(), rustls_hello(&[b"h2", b"http/1.1"], "www.example.com")));
    v
}

mod agree;

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--agree") {
        agree::run(&inputs());
        return;
    }
    println!("input\tparser\tmedian ns\tmin ns");
    for (name, body) in inputs() {
        let rec = record(&body);
        let (a, b) = (ours(&rec), theirs(&rec));
        assert_eq!(a, b, "{name}: check values differ");
        let label = format!("{name} ({}B)", rec.len());
        bench("verilith-tls", &label, || ours(black_box(&rec)));
        bench("rustls Acceptor", &label, || theirs(black_box(&rec)));
    }
}
