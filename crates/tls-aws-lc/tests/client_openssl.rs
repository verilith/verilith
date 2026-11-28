//! The verified client against `openssl s_server` over TCP. Skipped (with
//! a note) where there is no `openssl` binary.
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};
use verilith_tls_aws_lc::client::{config, TlsStream};
use verilith_tls_aws_lc::*;

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
const CA: &[u8] = include_bytes!("data/ca.der");

struct Server(Child, u16);

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn openssl(args: &[&str]) -> Option<Server> {
    if Command::new("openssl").arg("version").output().is_err() {
        eprintln!("no openssl binary: skipped");
        return None;
    }
    let port = free_port();
    let child = Command::new("openssl")
        .args(["s_server", "-tls1_3", "-www", "-accept", &port.to_string()])
        .args(["-certform", "DER", "-cert", &format!("{DATA}/leaf.der")])
        .args(["-keyform", "DER", "-key", &format!("{DATA}/leaf.key.der")])
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let start = Instant::now();
    while TcpStream::connect(("127.0.0.1", port)).is_err() {
        assert!(start.elapsed() < Duration::from_secs(10), "s_server did not start");
        std::thread::sleep(Duration::from_millis(50));
    }
    Some(Server(child, port))
}

/// `GET /` from s_server's -www page, which reports the session.
fn get(port: u16, cfg: verilith_tls::client_hs::ClientConfig) -> std::io::Result<String> {
    let tcp = TcpStream::connect(("127.0.0.1", port))?;
    tcp.set_read_timeout(Some(Duration::from_secs(10)))?;
    let mut t = TlsStream::connect(Arc::new(cfg), "localhost", tcp)?;
    t.write_all(b"GET / HTTP/1.0\r\n\r\n")?;
    let mut page = Vec::new();
    // s_server -www closes the TCP connection after the page, with or
    // without close_notify depending on the version.
    let _ = t.read_to_end(&mut page);
    Ok(String::from_utf8_lossy(&page).into_owned())
}

#[test]
fn default_config() {
    let Some(s) = openssl(&[]) else { return };
    let page = get(s.1, config(vec![CA.to_vec()], &[])).unwrap();
    assert!(page.contains("Protocol  : TLSv1.3"), "{page}");
}

#[test]
fn each_suite() {
    for (suite, name) in [
        (TLS_AES_128_GCM_SHA256, "TLS_AES_128_GCM_SHA256"),
        (TLS_AES_256_GCM_SHA384, "TLS_AES_256_GCM_SHA384"),
        (TLS_CHACHA20_POLY1305_SHA256, "TLS_CHACHA20_POLY1305_SHA256"),
    ] {
        let Some(s) = openssl(&["-ciphersuites", name]) else { return };
        let mut cfg = config(vec![CA.to_vec()], &[]);
        cfg.suites = vec![suite];
        let page = get(s.1, cfg).unwrap();
        assert!(page.contains(name), "{page}");
    }
}

#[test]
fn each_group_with_retry() {
    // The client's shares are X25519MLKEM768 and X25519; OpenSSL 3.0 has
    // no hybrid, so X25519 takes the second share and P-256 and P-384 need a
    // HelloRetryRequest.
    for g in ["X25519", "P-256", "P-384"] {
        let Some(s) = openssl(&["-groups", g]) else { return };
        let page = get(s.1, config(vec![CA.to_vec()], &[])).unwrap();
        assert!(page.contains("TLSv1.3"), "{g}: {page}");
    }
}

#[test]
fn certificate_request() {
    let Some(s) = openssl(&["-verify", "1"]) else { return };
    let page = get(s.1, config(vec![CA.to_vec()], &[])).unwrap();
    assert!(page.contains("TLSv1.3"), "{page}");
}

#[test]
fn wrong_name_and_ca() {
    let Some(s) = openssl(&[]) else { return };
    let tcp = TcpStream::connect(("127.0.0.1", s.1)).unwrap();
    let e = TlsStream::connect(Arc::new(config(vec![CA.to_vec()], &[])), "example.org", tcp).err().unwrap();
    assert!(e.to_string().contains("alert 42"), "{e}");
    let tcp = TcpStream::connect(("127.0.0.1", s.1)).unwrap();
    let leaf = include_bytes!("data/leaf.der").to_vec();
    let e = TlsStream::connect(Arc::new(config(vec![leaf], &[])), "localhost", tcp).err().unwrap();
    assert!(e.to_string().contains("alert 48"), "{e}");
}

#[test]
fn alpn() {
    let Some(s) = openssl(&["-alpn", "h2,http/1.1"]) else { return };
    let tcp = TcpStream::connect(("127.0.0.1", s.1)).unwrap();
    let t = TlsStream::connect(Arc::new(config(vec![CA.to_vec()], &[b"http/1.1"])), "localhost", tcp).unwrap();
    assert_eq!(t.alpn(), Some(&b"http/1.1"[..]));
}
