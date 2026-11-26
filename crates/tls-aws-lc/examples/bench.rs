//! verilith-tls against rustls 0.23 as a TLS 1.3 server, both over aws-lc:
//! full handshakes, and record throughput. A rustls client drives both;
//! only the server's own work is timed.
//!
//!     cargo run --release --example bench
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore, ServerConfig, ServerConnection};
use std::io::{Read, Write};
use std::sync::Arc;
use std::time::{Duration, Instant};
use verilith_tls::server::Config;
use verilith_tls::stream::ServerStream;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("../tests/data/leaf.der");
const CA: &[u8] = include_bytes!("../tests/data/ca.der");
const KEY: &[u8] = include_bytes!("../tests/data/leaf.key.der");

trait Server {
    fn feed(&mut self, data: &[u8]) -> Vec<u8>;
    fn read_plain(&mut self, out: &mut Vec<u8>);
    fn send(&mut self, data: &[u8]) -> Vec<u8>;
}

struct Ours(ServerStream<AwsLc>);
impl Server for Ours {
    fn feed(&mut self, data: &[u8]) -> Vec<u8> {
        self.0.read_tls(data);
        self.0.process().unwrap();
        self.0.take_pending()
    }
    fn read_plain(&mut self, out: &mut Vec<u8>) {
        out.extend_from_slice(self.0.plaintext());
        let n = self.0.plaintext().len();
        self.0.consume_plaintext(n);
    }
    fn send(&mut self, data: &[u8]) -> Vec<u8> {
        self.0.write(data).unwrap();
        self.0.take_pending()
    }
}

struct Theirs(ServerConnection);
impl Server for Theirs {
    fn feed(&mut self, mut data: &[u8]) -> Vec<u8> {
        while !data.is_empty() {
            self.0.read_tls(&mut data).unwrap();
            self.0.process_new_packets().unwrap();
        }
        let mut out = Vec::new();
        while self.0.wants_write() {
            self.0.write_tls(&mut out).unwrap();
        }
        out
    }
    fn read_plain(&mut self, out: &mut Vec<u8>) {
        let _ = self.0.reader().read_to_end(out);
    }
    fn send(&mut self, data: &[u8]) -> Vec<u8> {
        self.0.writer().write_all(data).unwrap();
        let mut out = Vec::new();
        while self.0.wants_write() {
            self.0.write_tls(&mut out).unwrap();
        }
        out
    }
}

fn client_config(group: &'static dyn rustls::crypto::SupportedKxGroup) -> Arc<ClientConfig> {
    let mut roots = RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    let mut provider = rustls::crypto::aws_lc_rs::default_provider();
    provider.kx_groups = vec![group];
    provider.cipher_suites = vec![rustls::crypto::aws_lc_rs::cipher_suite::TLS13_AES_128_GCM_SHA256];
    let mut c = ClientConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    c.alpn_protocols = vec![b"h2".to_vec()];
    c.resumption = rustls::client::Resumption::disabled();
    Arc::new(c)
}

/// One handshake; returns the server's time and the connected pair.
fn handshake<S: Server>(cc: &Arc<ClientConfig>, mut s: S) -> (Duration, ClientConnection, S) {
    let mut c = ClientConnection::new(cc.clone(), ServerName::try_from("localhost").unwrap()).unwrap();
    let mut t = Duration::ZERO;
    for _ in 0..4 {
        let mut buf = Vec::new();
        while c.wants_write() {
            c.write_tls(&mut buf).unwrap();
        }
        if buf.is_empty() {
            break;
        }
        let t0 = Instant::now();
        let out = s.feed(&buf);
        t += t0.elapsed();
        let mut rd = &out[..];
        while !rd.is_empty() {
            c.read_tls(&mut rd).unwrap();
            c.process_new_packets().unwrap();
        }
    }
    assert!(!c.is_handshaking());
    (t, c, s)
}

fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[v.len() / 2]
}

fn main() {
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    let ours_cfg = Arc::new(
        Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), b"\x02h2".to_vec(), &vec![LEAF.to_vec()])
            .unwrap(),
    );
    let mut theirs_cfg = ServerConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(
            vec![CertificateDer::from(LEAF.to_vec())],
            PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(KEY.to_vec())),
        )
        .unwrap();
    theirs_cfg.alpn_protocols = vec![b"h2".to_vec()];
    theirs_cfg.session_storage = Arc::new(rustls::server::NoServerSessionStorage {});
    theirs_cfg.send_tls13_tickets = 0;
    let theirs_cfg = Arc::new(theirs_cfg);
    let new_ours = || Ours(ServerStream::new(ours_cfg.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap()))));
    let new_theirs = || Theirs(ServerConnection::new(theirs_cfg.clone()).unwrap());

    use rustls::crypto::aws_lc_rs::kx_group;
    println!("Full handshake, server side, ECDSA P-256 certificate, AES-128-GCM (median of 9 runs of 300, us)");
    println!("| group | verilith-tls | rustls 0.23 |");
    println!("|---|---:|---:|");
    for (name, g) in [("X25519", kx_group::X25519), ("P-256", kx_group::SECP256R1), ("X25519MLKEM768", kx_group::X25519MLKEM768)] {
        let cc = client_config(g);
        let mut a = Vec::new();
        let mut b = Vec::new();
        for _ in 0..9 {
            let mut ta = Duration::ZERO;
            let mut tb = Duration::ZERO;
            for _ in 0..300 {
                ta += handshake(&cc, new_ours()).0;
                tb += handshake(&cc, new_theirs()).0;
            }
            a.push(ta.as_secs_f64() * 1e6 / 300.0);
            b.push(tb.as_secs_f64() * 1e6 / 300.0);
        }
        println!("| {} | {:.1} | {:.1} |", name, median(a), median(b));
    }

    // Throughput: 16 MiB each way, in 16 KiB writes.
    let cc = client_config(kx_group::X25519);
    let chunk = vec![0x5au8; 16384];
    let total = 16 << 20;
    println!();
    println!("Records, 16 MiB in 16 KiB pieces, AES-128-GCM (median of 9, GB/s)");
    println!("| direction | verilith-tls | rustls 0.23 |");
    println!("|---|---:|---:|");
    let mut res = [[Vec::new(), Vec::new()], [Vec::new(), Vec::new()]];
    for _ in 0..9 {
        for which in 0..2 {
            // Server sends.
            let (t_send, t_recv) = if which == 0 {
                run_throughput(&cc, new_ours(), &chunk, total)
            } else {
                run_throughput(&cc, new_theirs(), &chunk, total)
            };
            res[0][which].push(total as f64 / t_send.as_secs_f64() / 1e9);
            res[1][which].push(total as f64 / t_recv.as_secs_f64() / 1e9);
        }
    }
    let [send, recv] = res;
    let [sa, sb] = send;
    let [ra, rb] = recv;
    println!("| server seals | {:.2} | {:.2} |", median(sa), median(sb));
    println!("| server opens | {:.2} | {:.2} |", median(ra), median(rb));
}

fn run_throughput<S: Server>(cc: &Arc<ClientConfig>, s: S, chunk: &[u8], total: usize) -> (Duration, Duration) {
    let (_, mut c, mut s) = handshake(cc, s);
    // Seal.
    let t0 = Instant::now();
    let mut sent = 0;
    let mut sink = 0usize;
    while sent < total {
        let out = s.send(chunk);
        sink += out.len();
        sent += chunk.len();
    }
    let t_send = t0.elapsed();
    std::hint::black_box(sink);
    // Open: the client's records, made beforehand.
    c.set_buffer_limit(None);
    let mut recs = Vec::new();
    let mut n = 0;
    while n < total {
        c.writer().write_all(chunk).unwrap();
        while c.wants_write() {
            c.write_tls(&mut recs).unwrap();
        }
        n += chunk.len();
    }
    let mut plain = Vec::with_capacity(total);
    let t0 = Instant::now();
    for piece in recs.chunks(16 * 1024 + 22) {
        s.feed(piece);
        s.read_plain(&mut plain);
        plain.clear();
    }
    let t_recv = t0.elapsed();
    (t_send, t_recv)
}
