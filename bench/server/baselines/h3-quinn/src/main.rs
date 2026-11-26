//! HTTP/3 baseline for bench/server: h3 on quinn.
//!
//!   h3-quinn-hello --threads N --h3 PORT --cert C --key K --root DIR
//!
//! Routes (the same for every server in the comparison):
//!   GET /plaintext       13 bytes, "Hello, World!", text/plain
//!   GET /static/<name>   a file under DIR, read into memory at start
//! Every response carries Server and Date.
//!
//! quinn drives each endpoint from one task, so one endpoint on a
//! multi-threaded runtime tops out near one core. To give quinn its best
//! showing on N cores, each of the N threads runs its own current-thread
//! runtime and its own endpoint on an SO_REUSEPORT socket bound to the same
//! port; the kernel spreads clients across them by 4-tuple, the way nginx
//! and h2o spread QUIC across workers.
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::{Arc, RwLock};
use std::time::Duration;

use bytes::Bytes;
use http::header::{CONTENT_LENGTH, CONTENT_TYPE, DATE, SERVER};
use http::{HeaderValue, Response, StatusCode};

struct State {
    files: HashMap<String, Bytes>,
    date: RwLock<HeaderValue>,
}

fn now() -> HeaderValue {
    HeaderValue::from_str(&httpdate::fmt_http_date(std::time::SystemTime::now())).unwrap()
}

fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter().position(|a| a == k).map(|i| args[i + 1].clone())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let threads: usize = arg(&args, "--threads").map_or(1, |s| s.parse().unwrap());
    let port: u16 = arg(&args, "--h3").expect("--h3").parse().unwrap();
    let root = arg(&args, "--root").expect("--root");
    let mut files = HashMap::new();
    for e in std::fs::read_dir(&root).unwrap() {
        let e = e.unwrap();
        if e.file_type().unwrap().is_file() {
            files.insert(e.file_name().into_string().unwrap(), Bytes::from(std::fs::read(e.path()).unwrap()));
        }
    }
    let st = Arc::new(State { files, date: RwLock::new(now()) });
    let crypto = tls_config(&arg(&args, "--cert").expect("--cert"), &arg(&args, "--key").expect("--key"));
    let st2 = st.clone();
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(Duration::from_millis(500));
            *st2.date.write().unwrap() = now();
        }
    });
    let addr = SocketAddr::from(([127, 0, 0, 1], port));
    let mut hs = Vec::new();
    for _ in 0..threads {
        let sock = reuseport_socket(addr);
        let (st, crypto) = (st.clone(), crypto.clone());
        hs.push(std::thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().unwrap();
            rt.block_on(endpoint(st, crypto, sock));
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
}

fn reuseport_socket(addr: SocketAddr) -> std::net::UdpSocket {
    use socket2::{Domain, Protocol, Socket, Type};
    let s = Socket::new(Domain::IPV4, Type::DGRAM, Some(Protocol::UDP)).unwrap();
    s.set_reuse_port(true).unwrap();
    // Room for bursts from many clients between reads.
    let _ = s.set_recv_buffer_size(8 << 20);
    let _ = s.set_send_buffer_size(8 << 20);
    s.bind(&addr.into()).unwrap();
    s.into()
}

fn tls_config(cert: &str, key: &str) -> Arc<quinn::crypto::rustls::QuicServerConfig> {
    let certs = rustls_pemfile::certs(&mut std::io::BufReader::new(std::fs::File::open(cert).unwrap()))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let key = rustls_pemfile::private_key(&mut std::io::BufReader::new(std::fs::File::open(key).unwrap()))
        .unwrap()
        .unwrap();
    let mut c = rustls::ServerConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .unwrap();
    c.alpn_protocols = vec![b"h3".to_vec()];
    c.max_early_data_size = u32::MAX;
    Arc::new(quinn::crypto::rustls::QuicServerConfig::try_from(c).unwrap())
}

async fn endpoint(st: Arc<State>, crypto: Arc<quinn::crypto::rustls::QuicServerConfig>, sock: std::net::UdpSocket) {
    let mut cfg = quinn::ServerConfig::with_crypto(crypto);
    let mut t = quinn::TransportConfig::default();
    // The same stream limit as the HTTP/2 servers, and windows large enough
    // that a 64 KiB response never waits on flow control.
    t.max_concurrent_bidi_streams(256u32.into());
    t.stream_receive_window((1u32 << 20).into());
    t.receive_window((16u32 << 20).into());
    t.send_window(16 << 20);
    t.max_idle_timeout(Some(Duration::from_secs(30).try_into().unwrap()));
    cfg.transport_config(Arc::new(t));
    let ep = quinn::Endpoint::new(quinn::EndpointConfig::default(), Some(cfg), sock, Arc::new(quinn::TokioRuntime))
        .unwrap();
    while let Some(inc) = ep.accept().await {
        let st = st.clone();
        tokio::spawn(async move {
            if let Ok(conn) = inc.await {
                let _ = connection(st, conn).await;
            }
        });
    }
}

async fn connection(st: Arc<State>, conn: quinn::Connection) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut h = h3::server::builder().build::<_, Bytes>(h3_quinn::Connection::new(conn)).await?;
    while let Some(resolver) = h.accept().await? {
        let st = st.clone();
        tokio::spawn(async move {
            let Ok((req, mut stream)) = resolver.resolve_request().await else { return };
            // Read the request to its end (a GET's empty body and FIN), so
            // that quinn does not answer the client's FIN with STOP_SENDING
            // (code 0, which clients count as an error) when the stream drops.
            while let Ok(Some(_)) = stream.recv_data().await {}
            let path = req.uri().path();
            let (status, ctype, body) = if path == "/plaintext" {
                (StatusCode::OK, "text/plain", Bytes::from_static(b"Hello, World!"))
            } else if let Some(b) = path.strip_prefix("/static/").and_then(|n| st.files.get(n)) {
                (StatusCode::OK, "application/octet-stream", b.clone())
            } else {
                (StatusCode::NOT_FOUND, "text/plain", Bytes::from_static(b"not found"))
            };
            let mut r = Response::new(());
            *r.status_mut() = status;
            let hd = r.headers_mut();
            hd.insert(SERVER, HeaderValue::from_static("h3-quinn"));
            hd.insert(DATE, st.date.read().unwrap().clone());
            hd.insert(CONTENT_TYPE, HeaderValue::from_static(ctype));
            hd.insert(CONTENT_LENGTH, HeaderValue::from(body.len()));
            if stream.send_response(r).await.is_err() {
                return;
            }
            let _ = stream.send_data(body).await;
            let _ = stream.finish().await;
        });
    }
    Ok(())
}
