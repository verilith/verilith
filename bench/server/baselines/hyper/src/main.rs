//! hyper baseline for bench/server.
//!
//!   hyper-hello --threads N --http PORT [--h2c PORT] [--tls PORT --cert C --key K] --root DIR
//!
//! Routes (the same for every server in the comparison):
//!   GET /plaintext       13 bytes, "Hello, World!", text/plain
//!   GET /static/<name>   a file under DIR, read into memory at start
//! Every response carries Server and Date, as TechEmpower requires.
use std::collections::HashMap;
use std::convert::Infallible;
use std::net::SocketAddr;
use std::sync::{Arc, RwLock};
use std::time::Duration;

use bytes::Bytes;
use http_body_util::Full;
use hyper::body::Incoming;
use hyper::header::{CONTENT_TYPE, DATE, SERVER};
use hyper::{Request, Response, StatusCode};
use hyper_util::rt::{TokioExecutor, TokioIo};
use hyper_util::server::conn::auto;
use tokio::net::TcpListener;

struct State {
    files: HashMap<String, Bytes>,
    date: RwLock<hyper::header::HeaderValue>,
}

fn now() -> hyper::header::HeaderValue {
    hyper::header::HeaderValue::from_str(&httpdate::fmt_http_date(std::time::SystemTime::now())).unwrap()
}

async fn serve(st: Arc<State>, req: Request<Incoming>) -> Result<Response<Full<Bytes>>, Infallible> {
    let date = st.date.read().unwrap().clone();
    let path = req.uri().path();
    let (status, ctype, body) = if path == "/plaintext" {
        (StatusCode::OK, "text/plain", Bytes::from_static(b"Hello, World!"))
    } else if let Some(b) = path.strip_prefix("/static/").and_then(|n| st.files.get(n)) {
        (StatusCode::OK, "application/octet-stream", b.clone())
    } else {
        (StatusCode::NOT_FOUND, "text/plain", Bytes::from_static(b"not found"))
    };
    let mut r = Response::new(Full::new(body));
    *r.status_mut() = status;
    let h = r.headers_mut();
    h.insert(SERVER, hyper::header::HeaderValue::from_static("hyper"));
    h.insert(DATE, date);
    h.insert(CONTENT_TYPE, hyper::header::HeaderValue::from_static(ctype));
    Ok(r)
}

fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter().position(|a| a == k).map(|i| args[i + 1].clone())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let threads: usize = arg(&args, "--threads").map_or(1, |s| s.parse().unwrap());
    let root = arg(&args, "--root").expect("--root");
    let mut files = HashMap::new();
    for e in std::fs::read_dir(&root).unwrap() {
        let e = e.unwrap();
        if e.file_type().unwrap().is_file() {
            files.insert(e.file_name().into_string().unwrap(), Bytes::from(std::fs::read(e.path()).unwrap()));
        }
    }
    let st = Arc::new(State { files, date: RwLock::new(now()) });
    let rt = tokio::runtime::Builder::new_multi_thread().worker_threads(threads).enable_all().build().unwrap();
    rt.block_on(async move {
        let s2 = st.clone();
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(500)).await;
                *s2.date.write().unwrap() = now();
            }
        });
        let mut tasks = Vec::new();
        if let Some(p) = arg(&args, "--http") {
            tasks.push(tokio::spawn(listen(st.clone(), p.parse().unwrap(), None, false)));
        }
        if let Some(p) = arg(&args, "--h2c") {
            tasks.push(tokio::spawn(listen(st.clone(), p.parse().unwrap(), None, true)));
        }
        if let Some(p) = arg(&args, "--tls") {
            let cfg = tls_config(&arg(&args, "--cert").unwrap(), &arg(&args, "--key").unwrap());
            tasks.push(tokio::spawn(listen(st.clone(), p.parse().unwrap(), Some(cfg), false)));
        }
        for t in tasks {
            t.await.unwrap();
        }
    });
}

fn tls_config(cert: &str, key: &str) -> Arc<tokio_rustls::rustls::ServerConfig> {
    use tokio_rustls::rustls;
    let certs = rustls_pemfile::certs(&mut std::io::BufReader::new(std::fs::File::open(cert).unwrap()))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let key = rustls_pemfile::private_key(&mut std::io::BufReader::new(std::fs::File::open(key).unwrap()))
        .unwrap()
        .unwrap();
    let mut c = rustls::ServerConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_safe_default_protocol_versions()
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .unwrap();
    c.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
    Arc::new(c)
}

async fn listen(st: Arc<State>, port: u16, tls: Option<Arc<tokio_rustls::rustls::ServerConfig>>, h2_only: bool) {
    let l = TcpListener::bind(SocketAddr::from(([127, 0, 0, 1], port))).await.unwrap();
    let acc = tls.map(tokio_rustls::TlsAcceptor::from);
    loop {
        let (s, _) = l.accept().await.unwrap();
        s.set_nodelay(true).unwrap();
        let st = st.clone();
        let acc = acc.clone();
        tokio::spawn(async move {
            let svc = hyper::service::service_fn(move |r| serve(st.clone(), r));
            let mut b = auto::Builder::new(TokioExecutor::new());
            b.http1().keep_alive(true).pipeline_flush(true);
            b.http2().max_concurrent_streams(256);
            if h2_only {
                let b = b.http2_only();
                let _ = b.serve_connection(TokioIo::new(s), svc).await;
            } else if let Some(acc) = acc {
                if let Ok(t) = acc.accept(s).await {
                    let _ = b.serve_connection(TokioIo::new(t), svc).await;
                }
            } else {
                let _ = b.serve_connection(TokioIo::new(s), svc).await;
            }
        });
    }
}
