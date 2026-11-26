//! verilith-quic-conn's server against quinn-proto's client, in memory
//! with a virtual clock: handshakes, request/response streams both ways,
//! large transfers, loss and reordering, flow control, and closes.
use bytes::BytesMut;
use quinn_proto::{ClientConfig, ConnectionHandle, DatagramEvent, Dir, Endpoint, EndpointConfig, Event as QEvent};
use rustls::pki_types::CertificateDer;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::sync::Arc;
use std::time::{Duration, Instant};
use verilith_quic_conn::{Config, Datagram, Event, Server, StreamError};
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("../../tls-aws-lc/tests/data/leaf.der");
const CA: &[u8] = include_bytes!("../../tls-aws-lc/tests/data/ca.der");
const KEY: &[u8] = include_bytes!("../../tls-aws-lc/tests/data/leaf.key.der");

pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn server_config(f: impl Fn(&mut Config<AwsLc>)) -> Arc<Config<AwsLc>> {
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    let schemes = key.schemes().to_vec();
    let tls = verilith_tls::server::Config::new(SUITES.to_vec(), GROUPS.to_vec(), schemes, b"\x02h3".to_vec(), &vec![LEAF.to_vec()]).unwrap();
    let key = Arc::new(key);
    let mut c = Config::new(Arc::new(tls), Arc::new(move || AwsLc::shared(key.clone())));
    f(&mut c);
    Arc::new(c)
}

fn client_config() -> ClientConfig {
    let mut roots = rustls::RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    let provider = rustls::crypto::aws_lc_rs::default_provider();
    let mut c = rustls::ClientConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    c.alpn_protocols = vec![b"h3".to_vec()];
    let q = quinn_proto::crypto::rustls::QuicClientConfig::try_from(c).unwrap();
    let mut cc = ClientConfig::new(Arc::new(q));
    let mut t = quinn_proto::TransportConfig::default();
    t.max_idle_timeout(Some(Duration::from_secs(60).try_into().unwrap()));
    cc.transport_config(Arc::new(t));
    cc
}

/// The network: datagrams in flight with their arrival times, and loss.
pub struct Net {
    pub now: Instant,
    pub epoch: Instant,
    pub delay: Duration,
    pub loss: u64, // per mille
    pub reorder: u64,
    pub rng: Rng,
    to_server: Vec<(Instant, Vec<u8>)>,
    to_client: Vec<(Instant, Vec<u8>)>,
    pub server_bytes: usize,
}

pub struct Pair {
    pub net: Net,
    pub client: Endpoint,
    pub ch: ConnectionHandle,
    pub c: quinn_proto::Connection,
    pub server: Server<AwsLc>,
    pub conn: Option<usize>,
    client_addr: SocketAddr,
    server_addr: SocketAddr,
    buf: Vec<u8>,
}

impl Pair {
    pub fn new(cfg: Arc<Config<AwsLc>>, delay: Duration, loss: u64, seed: u64) -> Pair {
        let now = Instant::now();
        let mut client = Endpoint::new(Arc::new(EndpointConfig::default()), None, true, None);
        let server_addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 1), 443));
        let client_addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(10, 0, 0, 2), 5000));
        let (ch, c) = client.connect(now, client_config(), server_addr, "localhost").unwrap();
        Pair {
            net: Net { now, epoch: now, delay, loss, reorder: 0, rng: Rng(seed | 1), to_server: Vec::new(), to_client: Vec::new(), server_bytes: 0 },
            client,
            ch,
            c,
            server: Server::new(cfg),
            conn: None,
            client_addr,
            server_addr,
            buf: Vec::new(),
        }
    }

    fn micros(&self) -> u64 {
        (self.net.now - self.net.epoch).as_micros() as u64
    }

    fn lose(&mut self) -> bool {
        self.net.loss > 0 && self.net.rng.next() % 1000 < self.net.loss
    }

    fn jitter(&mut self) -> Duration {
        if self.net.reorder > 0 { Duration::from_micros(self.net.rng.next() % self.net.reorder) } else { Duration::ZERO }
    }

    /// Moves everything that can move now; true if anything did.
    fn step(&mut self) -> bool {
        let mut moved = false;
        // Client to network.
        loop {
            self.buf.clear();
            let Some(t) = self.c.poll_transmit(self.net.now, 10, &mut self.buf) else { break };
            let seg = t.segment_size.unwrap_or(t.size);
            let all = self.buf[..t.size].to_vec();
            for d in all.chunks(seg) {
                if !self.lose() {
                    let at = self.net.now + self.net.delay + self.jitter();
                    self.net.to_server.push((at, d.to_vec()));
                }
            }
            moved = true;
        }
        while let Some(ev) = self.c.poll_endpoint_events() {
            if let Some(back) = self.client.handle_event(self.ch, ev) {
                self.c.handle_event(back);
            }
        }
        // Network to server.
        let now = self.net.now;
        let mut due: Vec<(Instant, Vec<u8>)> = Vec::new();
        self.net.to_server.retain(|d| {
            if d.0 <= now {
                due.push(d.clone());
                false
            } else {
                true
            }
        });
        due.sort_by_key(|d| d.0);
        let us = self.micros();
        for (_, mut d) in due {
            let mut out = Vec::new();
            match self.server.handle(us, &mut d, &mut out) {
                Datagram::Conn(i) => self.conn = Some(i),
                _ => {}
            }
            moved = true;
        }
        // Server to network.
        if let Some(i) = self.conn {
            let mut buf = Vec::new();
            loop {
                let Some(c) = self.server.conn(i) else { break };
                let Some(t) = c.poll_transmit(us, 16, &mut buf) else { break };
                let seg = t.segment_size.unwrap_or(t.size);
                self.net.server_bytes += t.size;
                for d in buf[..t.size].chunks(seg) {
                    assert!(d.len() <= 1452);
                    if !self.lose() {
                        let at = self.net.now + self.net.delay + self.jitter();
                        self.net.to_client.push((at, d.to_vec()));
                    }
                }
                moved = true;
            }
        }
        // Network to client.
        let mut due: Vec<(Instant, Vec<u8>)> = Vec::new();
        self.net.to_client.retain(|d| {
            if d.0 <= now {
                due.push(d.clone());
                false
            } else {
                true
            }
        });
        due.sort_by_key(|d| d.0);
        for (_, d) in due {
            let mut resp = Vec::new();
            match self.client.handle(now, self.server_addr, None, None, BytesMut::from(&d[..]), &mut resp) {
                Some(DatagramEvent::ConnectionEvent(_, ev)) => self.c.handle_event(ev),
                _ => {}
            }
            moved = true;
        }
        let _ = self.client_addr;
        moved
    }

    /// Advances the clock to the next event: a datagram arriving or a
    /// timer. False if there is none.
    fn advance(&mut self) -> bool {
        let mut next: Option<Instant> = None;
        let mut min = |t: Instant| next = Some(next.map_or(t, |n: Instant| n.min(t)));
        for d in self.net.to_server.iter().chain(self.net.to_client.iter()) {
            min(d.0);
        }
        if let Some(t) = self.c.poll_timeout() {
            min(t);
        }
        if let Some(i) = self.conn {
            if let Some(c) = self.server.conn(i) {
                if let Some(t) = c.poll_timeout() {
                    if std::env::var_os("VQ_TRACE").is_some() {
                        eprintln!("server timeout at {t}");
                    }
                    min(self.net.epoch + Duration::from_micros(t));
                }
            }
        }
        let Some(t) = next else { return false };
        if t > self.net.now {
            self.net.now = t;
        }
        let now = self.net.now;
        if self.c.poll_timeout().is_some_and(|t| t <= now) {
            self.c.handle_timeout(now);
        }
        let us = self.micros();
        if let Some(i) = self.conn {
            if let Some(c) = self.server.conn(i) {
                if c.poll_timeout().is_some_and(|t| t <= us) {
                    c.handle_timeout(us);
                }
            }
        }
        true
    }

    /// Runs until `done` holds, or the virtual time limit.
    pub fn run(&mut self, limit: Duration, mut done: impl FnMut(&mut Pair) -> bool) -> bool {
        let end = self.net.now + limit;
        loop {
            while self.step() {
                if done(self) {
                    return true;
                }
            }
            if done(self) {
                return true;
            }
            if self.net.now > end || !self.advance() {
                return false;
            }
        }
    }

    pub fn sconn(&mut self) -> &mut verilith_quic_conn::Connection<AwsLc> {
        let i = self.conn.unwrap();
        self.server.conn(i).unwrap()
    }
}

/// An echo-ish server: for each request stream, reads it all, then
/// answers with `size(request)` bytes.
pub fn serve(p: &mut Pair, reqs: &mut std::collections::HashMap<u64, Vec<u8>>, resp: &mut std::collections::HashMap<u64, (Vec<u8>, usize)>, size: &dyn Fn(&[u8]) -> usize) {
    let Some(i) = p.conn else { return };
    let Some(c) = p.server.conn(i) else { return };
    while let Some(ev) = c.poll() {
        if let Event::Closed { code, .. } = ev {
            panic!("server closed: {code:#x}");
        }
    }
    while let Some(id) = c.accept(true) {
        reqs.insert(id, Vec::new());
    }
    let ids: Vec<u64> = reqs.keys().copied().collect();
    for id in ids {
        let buf = reqs.get_mut(&id).unwrap();
        loop {
            match c.read(id, buf, 65536) {
                Ok((_, true)) => {
                    let n = size(buf);
                    let body: Vec<u8> = (0..n).map(|k| (k % 251) as u8).collect();
                    resp.insert(id, (body, 0));
                    reqs.remove(&id);
                    break;
                }
                Ok(_) => continue,
                Err(StreamError::Blocked) => break,
                Err(e) => panic!("read {id}: {e:?}"),
            }
        }
    }
    let ids: Vec<u64> = resp.keys().copied().collect();
    for id in ids {
        let (body, off) = resp.get_mut(&id).unwrap();
        while *off < body.len() {
            match c.write(id, &body[*off..]) {
                Ok(n) => *off += n,
                Err(StreamError::Blocked) => break,
                Err(e) => panic!("write {id}: {e:?}"),
            }
        }
        if *off == body.len() {
            c.finish(id).unwrap();
            resp.remove(&id);
        }
    }
}

fn exchange(p: &mut Pair, requests: &[(Vec<u8>, usize)], limit: Duration) -> bool {
    use std::collections::HashMap;
    let mut sreqs = HashMap::new();
    let mut sresp = HashMap::new();
    let mut opened: Vec<(quinn_proto::StreamId, usize, Vec<u8>, bool, usize, usize)> = Vec::new();
    let mut next_req = 0;
    let sizes: HashMap<Vec<u8>, usize> = requests.iter().cloned().collect();
    let size = move |b: &[u8]| *sizes.get(b).unwrap_or_else(|| panic!("unknown request of {} bytes: {:?}", b.len(), &b[..b.len().min(20)]));
    let connected = p.run(limit, |p| p.c.is_handshaking() == false);
    assert!(connected, "handshake");
    p.run(limit, |p| {
        while let Some(ev) = p.c.poll() {
            if let QEvent::ConnectionLost { reason } = ev {
                let st = p.c.stats();
                panic!("client lost the connection: {reason}; tx frames {:?}; rx frames {:?}; path {:?}", st.frame_tx, st.frame_rx, st.path);
            }
        }
        while next_req < requests.len() {
            let Some(id) = p.c.streams().open(Dir::Bi) else {
                if std::env::var_os("VQ_TRACE").is_some() {
                    eprintln!("client: cannot open; handshaking {}", p.c.is_handshaking());
                }
                break;
            };
            if std::env::var_os("VQ_TRACE").is_some() {
                eprintln!("client opened {id}");
            }
            let (_, n) = &requests[next_req];
            opened.push((id, *n, Vec::new(), false, next_req, 0usize));
            next_req += 1;
        }
        for (id, _, _, _, k, w) in opened.iter_mut() {
            let req = &requests[*k].0;
            if *w > req.len() {
                continue;
            }
            let mut s = p.c.send_stream(*id);
            if *w < req.len() {
                if let Ok(n) = s.write(&req[*w..]) {
                    *w += n;
                }
            }
            if *w == req.len() {
                s.finish().unwrap();
                *w += 1;
            }
        }
        serve(p, &mut sreqs, &mut sresp, &size);
        for (id, _, got, fin, _, _) in opened.iter_mut() {
            if *fin {
                continue;
            }
            let mut rs = p.c.recv_stream(*id);
            let Ok(mut ch) = rs.read(true) else { continue };
            loop {
                match ch.next(usize::MAX) {
                    Ok(Some(c)) => got.extend_from_slice(&c.bytes),
                    Ok(None) => {
                        *fin = true;
                        break;
                    }
                    Err(_) => break,
                }
            }
            let _ = ch.finalize();
        }
        next_req == requests.len() && opened.iter().all(|o| o.3)
    }) && opened.iter().all(|(_, n, got, _, _, _)| got.len() == *n && got.iter().enumerate().all(|(k, &b)| b == (k % 251) as u8))
}

#[test]
fn handshake_and_one_request() {
    let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(10), 0, 1);
    assert!(exchange(&mut p, &[(b"GET /".to_vec(), 1000)], Duration::from_secs(10)));
    assert_eq!(p.sconn().alpn(), Some(&b"h3"[..]));
}

#[test]
fn many_requests_and_large_responses() {
    let mut p = Pair::new(server_config(|c| c.max_datagram = 1452), Duration::from_millis(5), 0, 2);
    let reqs: Vec<(Vec<u8>, usize)> = (0..300).map(|k| (format!("req {k}").into_bytes(), if k % 50 == 0 { 3_000_000 } else { k * 37 })).collect();
    assert!(exchange(&mut p, &reqs, Duration::from_secs(120)));
}

#[test]
fn lossy_path() {
    for seed in 1..6 {
        let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(20), 50, seed);
        p.net.reorder = 5_000;
        let reqs: Vec<(Vec<u8>, usize)> = (0..20).map(|k| (format!("req {k}").into_bytes(), 200_000 + k * 1000)).collect();
        assert!(exchange(&mut p, &reqs, Duration::from_secs(600)), "seed {seed}");
    }
}

#[test]
fn handshake_with_loss() {
    for seed in std::env::var("SEED").ok().map_or(1..30, |v| { let v: u64 = v.parse().unwrap(); v..v + 1 }) {
        eprintln!("seed {seed}");
        let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(30), 300, seed);
        assert!(exchange(&mut p, &[(b"x".to_vec(), 10)], Duration::from_secs(600)), "seed {seed}");
    }
}

#[test]
fn server_close_reaches_client() {
    let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(10), 0, 3);
    assert!(exchange(&mut p, &[(b"x".to_vec(), 10)], Duration::from_secs(10)));
    let now = p.micros();
    p.sconn().close(now, 0x100);
    let mut lost = false;
    p.run(Duration::from_secs(10), |p| {
        while let Some(ev) = p.c.poll() {
            if let QEvent::ConnectionLost { .. } = ev {
                lost = true;
            }
        }
        lost
    });
    assert!(lost);
    let _ = p.run(Duration::from_secs(10), |p| p.sconn().is_closed());
    assert!(p.sconn().is_closed());
}

#[test]
fn idle_timeout() {
    let mut p = Pair::new(server_config(|c| c.idle_timeout_ms = 2000), Duration::from_millis(10), 0, 4);
    assert!(exchange(&mut p, &[(b"x".to_vec(), 10)], Duration::from_secs(10)));
    // Silence the client: drop everything.
    p.net.loss = 1000;
    assert!(p.run(Duration::from_secs(30), |p| p.sconn().is_closed()));
}


#[test]
fn key_updates_from_the_client() {
    let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(5), 0, 5);
    assert!(exchange(&mut p, &[(b"a".to_vec(), 100_000)], Duration::from_secs(10)));
    for k in 0..3 {
        p.c.force_key_update();
        let reqs: Vec<(Vec<u8>, usize)> = (0..5).map(|j| (format!("k{k} {j}").into_bytes(), 50_000)).collect();
        assert!(exchange(&mut p, &reqs, Duration::from_secs(10)), "after update {k}");
    }
}

#[test]
fn small_flow_control_windows() {
    let mut p = Pair::new(
        server_config(|c| {
            c.stream_window = 4000;
            c.max_data = 10_000;
            c.max_streams_bidi = 3;
        }),
        Duration::from_millis(5),
        0,
        6,
    );
    // Requests bigger than the windows, more streams than allowed at once.
    let reqs: Vec<(Vec<u8>, usize)> = (0..20).map(|k| (vec![b'a' + k as u8; 9000 + k], 20_000)).collect();
    assert!(exchange(&mut p, &reqs, Duration::from_secs(60)));
}

#[test]
fn server_uni_stream_and_client_stop() {
    let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(5), 0, 7);
    assert!(exchange(&mut p, &[(b"x".to_vec(), 10)], Duration::from_secs(10)));
    // The server opens a unidirectional stream (as HTTP/3's control stream).
    let id = p.sconn().open(false).unwrap();
    assert_eq!(id, 3);
    p.sconn().write(id, b"\x00\x04\x00").unwrap();
    let mut got = Vec::new();
    assert!(p.run(Duration::from_secs(5), |p| {
        if let Some(sid) = p.c.streams().accept(Dir::Uni) {
            assert_eq!(u64::from(sid), 3);
        }
        let sid = quinn_proto::StreamId::new(quinn_proto::Side::Server, Dir::Uni, 0);
        let mut rs = p.c.recv_stream(sid);
        if let Ok(mut ch) = rs.read(true) {
            while let Ok(Some(c)) = ch.next(usize::MAX) {
                got.extend_from_slice(&c.bytes);
            }
            let _ = ch.finalize();
        }
        got == b"\x00\x04\x00"
    }));
    // The client asks the server to stop sending a response; the server
    // sees STOP_SENDING and resets.
    let sid = p.c.streams().open(Dir::Bi).unwrap();
    p.c.send_stream(sid).write(b"big").unwrap();
    p.c.send_stream(sid).finish().unwrap();
    let mut stopped = None;
    let mut wrote = false;
    assert!(p.run(Duration::from_secs(5), |p| {
        let c = p.sconn();
        while let Some(ev) = c.poll() {
            if let Event::Stopped { id, code } = ev {
                stopped = Some((id, code));
                c.reset(id, code).unwrap();
            }
        }
        if let Some(id) = c.accept(true) {
            let mut b = Vec::new();
            let _ = c.read(id, &mut b, 100);
            c.write(id, &vec![7u8; 1_000_000]).unwrap();
            wrote = true;
        }
        if wrote && stopped.is_none() {
            let _ = p.c.recv_stream(sid).stop(quinn_proto::VarInt::from_u32(9));
        }
        stopped.is_some()
    }));
    assert_eq!(stopped, Some((u64::from(sid), 9)));
    // The connection still works.
    assert!(exchange(&mut p, &[(b"after".to_vec(), 5000)], Duration::from_secs(10)));
}

#[test]
fn client_reset_request() {
    let mut p = Pair::new(server_config(|_| {}), Duration::from_millis(5), 0, 8);
    assert!(exchange(&mut p, &[(b"x".to_vec(), 10)], Duration::from_secs(10)));
    let sid = p.c.streams().open(Dir::Bi).unwrap();
    p.c.send_stream(sid).write(b"partial").unwrap();
    p.c.send_stream(sid).reset(quinn_proto::VarInt::from_u32(5)).unwrap();
    let mut seen = None;
    assert!(p.run(Duration::from_secs(5), |p| {
        let c = p.sconn();
        while c.poll().is_some() {}
        while let Some(id) = c.accept(true) {
            seen = Some(id);
        }
        if let Some(id) = seen {
            let mut b = Vec::new();
            loop {
                match c.read(id, &mut b, 100) {
                    Err(StreamError::Reset(5)) => return true,
                    Ok(_) => continue,
                    _ => return false,
                }
            }
        }
        false
    }));
}
