//! TLS: a rustls client talks to the engine in memory, over HTTP/1.1 and
//! h2 (by ALPN), with the ciphertext cut every way.
#![cfg(feature = "tls")]
use std::io::{Read, Write};
use std::sync::Arc;

use rustls::pki_types::{CertificateDer, ServerName};
use verilith_server::h1::{Ctx, Limits};
use verilith_server::tls::{Config, TlsConn};
use verilith_server::{Field, Limits2, Request, Response};

fn handler(req: &Request, res: &mut Response) {
    let mut body = req.target.to_vec();
    if req.target == b"/big" {
        body.resize(200_000, b'x');
    }
    let _ = res.send(200, &[Field { name: b"X-Test", value: b"1" }], &body);
}

#[derive(Clone, Copy, Debug)]
enum Backend {
    Verilith,
    #[cfg(feature = "tls-rustls")]
    Rustls,
}

const BACKENDS: &[Backend] = &[
    Backend::Verilith,
    #[cfg(feature = "tls-rustls")]
    Backend::Rustls,
];

fn configs(alpn: &[u8], backend: Backend) -> (Arc<Config>, Arc<rustls::ClientConfig>) {
    let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
    let cert = CertificateDer::from(c.cert.der().to_vec());
    let p = Arc::new(rustls::crypto::aws_lc_rs::default_provider());
    let s = match backend {
        Backend::Verilith => verilith_server::tls::config_der(vec![c.cert.der().to_vec()], &c.signing_key.serialize_der()).unwrap(),
        #[cfg(feature = "tls-rustls")]
        Backend::Rustls => {
            use rustls::pki_types::{PrivateKeyDer, PrivatePkcs8KeyDer};
            let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(c.signing_key.serialize_der()));
            let mut s = rustls::ServerConfig::builder_with_provider(p.clone())
                .with_safe_default_protocol_versions()
                .unwrap()
                .with_no_client_auth()
                .with_single_cert(vec![cert.clone()], key)
                .unwrap();
            s.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
            Arc::new(Config::Rustls(Arc::new(s)))
        }
    };
    let mut roots = rustls::RootCertStore::empty();
    roots.add(cert).unwrap();
    let mut cl = rustls::ClientConfig::builder_with_provider(p).with_safe_default_protocol_versions().unwrap().with_root_certificates(roots).with_no_client_auth();
    cl.alpn_protocols = vec![alpn.to_vec()];
    (s, Arc::new(cl))
}

/// Runs a client sending `request` plaintext; ciphertext to the server
/// goes in pieces of at most `chunk` bytes. Returns the client's plaintext.
fn talk(backend: Backend, alpn: &[u8], request: &[u8], chunk: usize) -> Vec<u8> {
    let (sc, cc) = configs(alpn, backend);
    let mut srv = TlsConn::new(sc, Limits::default(), Limits2::default()).unwrap();
    let mut cli = rustls::ClientConnection::new(cc, ServerName::try_from("localhost").unwrap()).unwrap();
    cli.writer().write_all(request).unwrap();
    let ctx = Ctx::new(b"t", b"Thu, 01 Jan 1970 00:00:00 GMT").unwrap();
    let mut got = Vec::new();
    for _ in 0..100_000 {
        let mut c2s = Vec::new();
        while cli.wants_write() {
            cli.write_tls(&mut c2s).unwrap();
        }
        let mut moved = !c2s.is_empty();
        let mut p = &c2s[..];
        while !p.is_empty() {
            let b = srv.read_buf();
            let n = b.len().min(p.len()).min(chunk);
            if n == 0 {
                srv.process(&handler, &ctx);
                continue;
            }
            b[..n].copy_from_slice(&p[..n]);
            srv.filled(n);
            p = &p[n..];
            srv.process(&handler, &ctx);
        }
        srv.process(&handler, &ctx);
        let mut s2c = Vec::new();
        loop {
            let mut v: [&[u8]; 8] = [&[]; 8];
            let k = srv.pending(&mut v);
            if k == 0 {
                break;
            }
            let n: usize = v[..k].iter().map(|s| s.len()).sum();
            for s in &v[..k] {
                s2c.extend_from_slice(s);
            }
            srv.wrote(n);
        }
        moved |= !s2c.is_empty();
        let mut r = &s2c[..];
        while !r.is_empty() {
            cli.read_tls(&mut r).unwrap();
            cli.process_new_packets().unwrap();
            let mut buf = [0u8; 65536];
            while let Ok(n) = cli.reader().read(&mut buf) {
                if n == 0 {
                    break;
                }
                got.extend_from_slice(&buf[..n]);
            }
        }
        if !moved {
            break;
        }
    }
    got
}

#[test]
fn http11_over_tls() {
    let req = b"GET /a HTTP/1.1\r\nHost: x\r\n\r\nGET /big HTTP/1.1\r\nHost: x\r\n\r\n";
    for &b in BACKENDS {
        for chunk in [1, 7, 100, 1 << 20] {
            let got = talk(b, b"http/1.1", req, chunk);
            let s = String::from_utf8_lossy(&got);
            assert!(s.starts_with("HTTP/1.1 200 OK\r\n"), "{b:?} chunk {chunk}");
            assert_eq!(s.matches("HTTP/1.1 200 OK").count(), 2, "{b:?} chunk {chunk}");
            assert!(got.ends_with(&[b'x'; 1000]), "{b:?} chunk {chunk}");
        }
    }
}

#[test]
fn h2_over_tls_by_alpn() {
    // The preface and an empty SETTINGS; the server's reply starts with its
    // SETTINGS frame (type 4 at byte 3).
    let mut req = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".to_vec();
    req.extend_from_slice(&[0, 0, 0, 4, 0, 0, 0, 0, 0]);
    for &b in BACKENDS {
        for chunk in [1, 50, 1 << 20] {
            let got = talk(b, b"h2", &req, chunk);
            assert!(got.len() >= 9 && got[3] == 4, "{b:?} chunk {chunk}: {got:?}");
        }
    }
}

#[test]
fn pem_decodes() {
    let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
    let pem = format!("junk\n{}{}", c.cert.pem(), c.signing_key.serialize_pem());
    assert_eq!(verilith_server::tls::pem_blocks(pem.as_bytes(), "CERTIFICATE"), vec![c.cert.der().to_vec()]);
    assert_eq!(verilith_server::tls::pem_blocks(pem.as_bytes(), "PRIVATE KEY"), vec![c.signing_key.serialize_der()]);
}
