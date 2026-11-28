//! Server CPU time of verilith-quic-conn against quinn-proto, each with a
//! quinn-proto client over an in-memory network with no delay and no
//! loss. Only the time spent in server calls is counted.
//!
//! `cargo run --release --example bench`
use bytes::{Bytes, BytesMut};
use quinn_proto::{
    ClientConfig, ConnectionHandle, DatagramEvent, Dir, Endpoint, EndpointConfig, Event as QEvent, ServerConfig, StreamEvent, TransportConfig,
};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use std::collections::HashMap;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::sync::Arc;
use std::time::{Duration, Instant};
use verilith_quic_conn::{Config, Datagram, Server, StreamError};
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("../../tls-aws-lc/tests/data/leaf.der");
const CA: &[u8] = include_bytes!("../../tls-aws-lc/tests/data/ca.der");
const KEY: &[u8] = include_bytes!("../../tls-aws-lc/tests/data/leaf.key.der");
const MTU: u16 = 1452;

fn rustls_provider() -> Arc<rustls::crypto::CryptoProvider> {
    Arc::new(rustls::crypto::aws_lc_rs::default_provider())
}

fn client_config() -> ClientConfig {
    let mut roots = rustls::RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    let mut c = rustls::ClientConfig::builder_with_provider(rustls_provider())
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    c.alpn_protocols = vec![b"h3".to_vec()];
    let mut cc = ClientConfig::new(Arc::new(quinn_proto::crypto::rustls::QuicClientConfig::try_from(c).unwrap()));
    cc.transport_config(Arc::new(transport()));
    cc
}

fn transport() -> TransportConfig {
    let mut t = TransportConfig::default();
    t.initial_mtu(MTU);
    t.mtu_discovery_config(None);
    t.max_idle_timeout(Some(Duration::from_secs(60).try_into().unwrap()));
    t.stream_receive_window((1u32 << 20).into());
    t.receive_window((16u32 << 20).into());
    t.send_window(8 << 20);
    t.max_concurrent_bidi_streams(100u32.into());
    t
}

/// A server under test.
trait Srv {
    /// A datagram from the client.
    fn recv(&mut self, now: Instant, d: &[u8]);
    /// Runs the application and collects datagrams to send.
    fn drive(&mut self, now: Instant, out: &mut Vec<Vec<u8>>);
    fn timeout(&mut self) -> Option<Instant>;
    fn on_timeout(&mut self, now: Instant);
}

/// Response size for a request: the request is the decimal size.
fn size_of(req: &[u8]) -> usize {
    std::str::from_utf8(req).unwrap().trim().parse().unwrap()
}

struct Ours {
    s: Server<AwsLc>,
    conns: Vec<usize>,
    epoch: Instant,
    reqs: HashMap<(usize, u64), Vec<u8>>,
    resp: HashMap<(usize, u64), (Bytes, usize)>,
    buf: Vec<u8>,
    body: Bytes,
}

impl Ours {
    fn new(epoch: Instant, body: Bytes) -> Ours {
        let key = Arc::new(SigningKey::from_pkcs8(KEY).unwrap());
        let tls = verilith_tls::server::Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), b"\x02h3".to_vec(), &vec![LEAF.to_vec()]).unwrap();
        let mut c = Config::new(Arc::new(tls), Arc::new(move || AwsLc::shared(key.clone())));
        c.max_datagram = MTU as usize;
        Ours { s: Server::new(Arc::new(c)), conns: Vec::new(), epoch, reqs: HashMap::new(), resp: HashMap::new(), buf: Vec::new(), body }
    }
    fn us(&self, now: Instant) -> u64 {
        (now - self.epoch).as_micros() as u64
    }
}

impl Srv for Ours {
    fn recv(&mut self, now: Instant, d: &[u8]) {
        let mut d = d.to_vec();
        let mut out = Vec::new();
        let t = self.us(now);
        if let Datagram::Conn(i) = self.s.handle(t, &mut d, &mut out) {
            if !self.conns.contains(&i) {
                self.conns.push(i);
            }
        }
    }
    fn drive(&mut self, now: Instant, out: &mut Vec<Vec<u8>>) {
        let t = self.us(now);
        for &i in &self.conns {
            let Some(c) = self.s.conn(i) else { continue };
            while c.poll().is_some() {}
            while let Some(id) = c.accept(true) {
                self.reqs.insert((i, id), Vec::new());
            }
            let keys: Vec<(usize, u64)> = self.reqs.keys().filter(|k| k.0 == i).copied().collect();
            for k in keys {
                let b = self.reqs.get_mut(&k).unwrap();
                loop {
                    match c.read(k.1, b, 65536) {
                        Ok((_, true)) => {
                            let n = size_of(b);
                            self.resp.insert(k, (self.body.slice(..n), 0));
                            self.reqs.remove(&k);
                            break;
                        }
                        Ok(_) => {}
                        Err(_) => break,
                    }
                }
            }
            let keys: Vec<(usize, u64)> = self.resp.keys().filter(|k| k.0 == i).copied().collect();
            for k in keys {
                let (b, off) = self.resp.get_mut(&k).unwrap();
                while *off < b.len() {
                    match c.write(k.1, &b[*off..]) {
                        Ok(n) => *off += n,
                        Err(StreamError::Blocked) => break,
                        Err(e) => panic!("{e:?}"),
                    }
                }
                if *off == b.len() {
                    c.finish(k.1).unwrap();
                    self.resp.remove(&k);
                }
            }
            loop {
                let Some(tx) = c.poll_transmit(t, 16, &mut self.buf) else { break };
                let seg = tx.segment_size.unwrap_or(tx.size);
                for d in self.buf[..tx.size].chunks(seg) {
                    out.push(d.to_vec());
                }
            }
        }
    }
    fn timeout(&mut self) -> Option<Instant> {
        let mut best: Option<u64> = None;
        for &i in &self.conns {
            if let Some(c) = self.s.conn(i) {
                if let Some(t) = c.poll_timeout() {
                    best = Some(best.map_or(t, |b| b.min(t)));
                }
            }
        }
        best.map(|t| self.epoch + Duration::from_micros(t))
    }
    fn on_timeout(&mut self, now: Instant) {
        let t = self.us(now);
        for &i in &self.conns {
            if let Some(c) = self.s.conn(i) {
                if c.poll_timeout().is_some_and(|x| x <= t) {
                    c.handle_timeout(t);
                }
            }
        }
    }
}

struct Quinn {
    ep: Endpoint,
    conns: HashMap<ConnectionHandle, quinn_proto::Connection>,
    reqs: HashMap<(ConnectionHandle, quinn_proto::StreamId), Vec<u8>>,
    resp: HashMap<(ConnectionHandle, quinn_proto::StreamId), Bytes>,
    body: Bytes,
    buf: Vec<u8>,
    client: SocketAddr,
}

impl Quinn {
    fn new(body: Bytes, client: SocketAddr) -> Quinn {
        let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(KEY.to_vec()));
        let mut c = rustls::ServerConfig::builder_with_provider(rustls_provider())
            .with_protocol_versions(&[&rustls::version::TLS13])
            .unwrap()
            .with_no_client_auth()
            .with_single_cert(vec![CertificateDer::from(LEAF.to_vec())], key)
            .unwrap();
        c.alpn_protocols = vec![b"h3".to_vec()];
        // Like ours: no session tickets, no 0-RTT.
        c.send_tls13_tickets = 0;
        let mut sc = ServerConfig::with_crypto(Arc::new(quinn_proto::crypto::rustls::QuicServerConfig::try_from(c).unwrap()));
        sc.transport_config(Arc::new(transport()));
        let ep = Endpoint::new(Arc::new(EndpointConfig::default()), Some(Arc::new(sc)), true, None);
        Quinn { ep, conns: HashMap::new(), reqs: HashMap::new(), resp: HashMap::new(), body, buf: Vec::new(), client }
    }
}

impl Srv for Quinn {
    fn recv(&mut self, now: Instant, d: &[u8]) {
        self.buf.clear();
        match self.ep.handle(now, self.client, None, None, BytesMut::from(d), &mut self.buf) {
            Some(DatagramEvent::NewConnection(inc)) => {
                self.buf.clear();
                if let Ok((ch, c)) = self.ep.accept(inc, now, &mut self.buf, None) {
                    self.conns.insert(ch, c);
                }
            }
            Some(DatagramEvent::ConnectionEvent(ch, ev)) => {
                if let Some(c) = self.conns.get_mut(&ch) {
                    c.handle_event(ev);
                }
            }
            _ => {}
        }
    }
    fn drive(&mut self, now: Instant, out: &mut Vec<Vec<u8>>) {
        for (&ch, c) in self.conns.iter_mut() {
            while let Some(ev) = c.poll_endpoint_events() {
                if let Some(back) = self.ep.handle_event(ch, ev) {
                    c.handle_event(back);
                }
            }
            while let Some(ev) = c.poll() {
                if let QEvent::Stream(StreamEvent::Opened { .. }) = ev {}
            }
            while let Some(id) = c.streams().accept(Dir::Bi) {
                self.reqs.insert((ch, id), Vec::new());
            }
            let keys: Vec<_> = self.reqs.keys().filter(|k| k.0 == ch).copied().collect();
            for k in keys {
                let mut rs = c.recv_stream(k.1);
                let Ok(mut chunks) = rs.read(true) else { continue };
                let mut fin = false;
                loop {
                    match chunks.next(usize::MAX) {
                        Ok(Some(x)) => self.reqs.get_mut(&k).unwrap().extend_from_slice(&x.bytes),
                        Ok(None) => {
                            fin = true;
                            break;
                        }
                        Err(_) => break,
                    }
                }
                let _ = chunks.finalize();
                if fin {
                    let n = size_of(&self.reqs.remove(&k).unwrap());
                    self.resp.insert(k, self.body.slice(..n));
                }
            }
            let keys: Vec<_> = self.resp.keys().filter(|k| k.0 == ch).copied().collect();
            for k in keys {
                let b = self.resp.get_mut(&k).unwrap();
                let mut s = c.send_stream(k.1);
                while !b.is_empty() {
                    match s.write_chunks(std::slice::from_mut(b)) {
                        Ok(w) if w.bytes > 0 => {}
                        _ => break,
                    }
                }
                if b.is_empty() {
                    let _ = s.finish();
                    self.resp.remove(&k);
                }
            }
            loop {
                self.buf.clear();
                let Some(t) = c.poll_transmit(now, 16, &mut self.buf) else { break };
                let seg = t.segment_size.unwrap_or(t.size);
                for d in self.buf[..t.size].chunks(seg) {
                    out.push(d.to_vec());
                }
            }
        }
    }
    fn timeout(&mut self) -> Option<Instant> {
        self.conns.values_mut().filter_map(|c| c.poll_timeout()).min()
    }
    fn on_timeout(&mut self, now: Instant) {
        for c in self.conns.values_mut() {
            if c.poll_timeout().is_some_and(|t| t <= now) {
                c.handle_timeout(now);
            }
        }
    }
}

struct Client {
    ep: Endpoint,
    conns: Vec<(ConnectionHandle, quinn_proto::Connection, Vec<(quinn_proto::StreamId, usize, usize, bool)>)>,
}

/// Runs `conns` connections, each making `reqs` requests of `size`
/// bytes, `parallel` at a time; returns the server's time.
fn run(srv: &mut dyn Srv, conns: usize, reqs: usize, size: usize, parallel: usize) -> Duration {
    let server_addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 1), 443));
    let mut cl = Client { ep: Endpoint::new(Arc::new(EndpointConfig::default()), None, true, None), conns: Vec::new() };
    let cc = client_config();
    for _ in 0..conns {
        let (ch, c) = cl.ep.connect(Instant::now(), cc.clone(), server_addr, "localhost").unwrap();
        cl.conns.push((ch, c, Vec::new()));
    }
    let mut spent = Duration::ZERO;
    let mut to_server: Vec<Vec<u8>> = Vec::new();
    let mut to_client: Vec<Vec<u8>> = Vec::new();
    let mut done = vec![0usize; conns];
    let mut opened = vec![0usize; conns];
    let mut buf = Vec::new();
    let req = format!("{size}");
    let start = Instant::now();
    loop {
        let now = Instant::now();
        // Client side.
        for (k, (ch, c, streams)) in cl.conns.iter_mut().enumerate() {
            for d in to_client.drain(..0) {
                let _ = d;
            }
            while let Some(ev) = c.poll() {
                if let QEvent::ConnectionLost { reason } = ev {
                    panic!("lost: {reason}");
                }
            }
            if !c.is_handshaking() {
                while opened[k] < reqs && streams.len() < parallel {
                    let Some(id) = c.streams().open(Dir::Bi) else { break };
                    c.send_stream(id).write(req.as_bytes()).unwrap();
                    c.send_stream(id).finish().unwrap();
                    streams.push((id, 0, size, false));
                    opened[k] += 1;
                }
            }
            streams.retain_mut(|(id, got, want, _)| {
                let mut rs = c.recv_stream(*id);
                let Ok(mut chunks) = rs.read(true) else { return true };
                let mut fin = false;
                loop {
                    match chunks.next(usize::MAX) {
                        Ok(Some(x)) => *got += x.bytes.len(),
                        Ok(None) => {
                            fin = true;
                            break;
                        }
                        Err(_) => break,
                    }
                }
                let _ = chunks.finalize();
                if fin {
                    assert_eq!(*got, *want);
                    done[k] += 1;
                }
                !fin
            });
            loop {
                buf.clear();
                let Some(t) = c.poll_transmit(now, 16, &mut buf) else { break };
                let seg = t.segment_size.unwrap_or(t.size);
                for d in buf[..t.size].chunks(seg) {
                    to_server.push(d.to_vec());
                }
            }
            while let Some(ev) = c.poll_endpoint_events() {
                if let Some(back) = cl.ep.handle_event(*ch, ev) {
                    c.handle_event(back);
                }
            }
            if c.poll_timeout().is_some_and(|t| t <= now) {
                c.handle_timeout(now);
            }
        }
        if done.iter().all(|&d| d == reqs) {
            break;
        }
        assert!(start.elapsed() < Duration::from_secs(120), "stuck: {done:?}");
        // Server side.
        let t0 = Instant::now();
        for d in to_server.drain(..) {
            srv.recv(now, &d);
        }
        if srv.timeout().is_some_and(|t| t <= now) {
            srv.on_timeout(now);
        }
        srv.drive(now, &mut to_client);
        spent += t0.elapsed();
        // Network to client.
        for d in to_client.drain(..) {
            let mut resp = Vec::new();
            if let Some(DatagramEvent::ConnectionEvent(ch, ev)) = cl.ep.handle(now, server_addr, None, None, BytesMut::from(&d[..]), &mut resp) {
                if let Some((_, c, _)) = cl.conns.iter_mut().find(|x| x.0 == ch) {
                    c.handle_event(ev);
                }
            }
        }
    }
    spent
}

fn main() {
    let body = Bytes::from(vec![0x5au8; 64 << 20]);
    let client = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 2), 5000));
    let cases: [(&str, usize, usize, usize, usize); 4] = [
        ("bulk: 1 connection, 4 x 64 MiB", 1, 4, 64 << 20, 1),
        ("requests: 1 connection, 20000 x 1 KiB, 50 at a time", 1, 20000, 1024, 50),
        ("requests: 10 connections, 2000 x 16 KiB each, 20 at a time", 10, 2000, 16 << 10, 20),
        ("handshakes: 500 connections, 1 x 1 KiB", 500, 1, 1024, 1),
    ];
    if let Ok(k) = std::env::var("ONLY") {
        // Profiling: one case, ours only, once.
        let (_, conns, reqs, size, par) = cases[k.parse::<usize>().unwrap()];
        let mut o = Ours::new(Instant::now(), body.clone());
        let t = run(&mut o, conns, reqs, size, par);
        println!("{:.1} ms", t.as_secs_f64() * 1e3);
        return;
    }
    println!("| case | verilith-quic-conn | quinn-proto |");
    println!("|---|---:|---:|");
    for (name, conns, reqs, size, par) in cases {
        let mut best = [Duration::MAX; 2];
        for _ in 0..3 {
            let epoch = Instant::now();
            let mut o = Ours::new(epoch, body.clone());
            best[0] = best[0].min(run(&mut o, conns, reqs, size, par));
            let mut q = Quinn::new(body.clone(), client);
            best[1] = best[1].min(run(&mut q, conns, reqs, size, par));
        }
        println!("| {name} | {:.1} ms | {:.1} ms |", best[0].as_secs_f64() * 1e3, best[1].as_secs_f64() * 1e3);
    }
}
