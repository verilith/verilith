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
    if req.early() {
        body.extend_from_slice(b" (early)");
    }
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
    talk_with(sc, cc, request, chunk).0
}

fn talk_with(sc: Arc<Config>, cc: Arc<rustls::ClientConfig>, request: &[u8], chunk: usize) -> (Vec<u8>, rustls::ClientConnection) {
    talk_early(sc, cc, b"", request, chunk)
}

/// [`talk_with`], sending `early` first as 0-RTT data if the client can
/// (and as ordinary data if not).
fn talk_early(sc: Arc<Config>, cc: Arc<rustls::ClientConfig>, early: &[u8], request: &[u8], chunk: usize) -> (Vec<u8>, rustls::ClientConnection) {
    let mut srv = TlsConn::new(sc, Limits::default(), Limits2::default()).unwrap();
    let mut cli = rustls::ClientConnection::new(cc, ServerName::try_from("localhost").unwrap()).unwrap();
    if !early.is_empty() {
        match cli.early_data() {
            Some(mut e) => e.write_all(early).unwrap(),
            None => cli.writer().write_all(early).unwrap(),
        }
    }
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
    (got, cli)
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

#[test]
fn tickets_resume() {
    for &b in BACKENDS {
        let (sc, cc) = configs(b"http/1.1", b);
        let req = b"GET /a HTTP/1.1\r\nHost: x\r\n\r\n";
        let (got, c1) = talk_with(sc.clone(), cc.clone(), req, 1 << 20);
        assert!(got.starts_with(b"HTTP/1.1 200"), "{b:?}");
        assert_eq!(c1.handshake_kind(), Some(rustls::HandshakeKind::Full), "{b:?}");
        let (got, c2) = talk_with(sc, cc, req, 7);
        assert!(got.starts_with(b"HTTP/1.1 200"), "{b:?}");
        assert_eq!(c2.handshake_kind(), Some(rustls::HandshakeKind::Resumed), "{b:?}");
    }
}

fn early_configs(alpn: &[u8]) -> (Arc<Config>, Arc<rustls::ClientConfig>) {
    let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
    let s = verilith_server::tls::config_der_early(vec![c.cert.der().to_vec()], &c.signing_key.serialize_der(), 16384).unwrap();
    let mut roots = rustls::RootCertStore::empty();
    roots.add(CertificateDer::from(c.cert.der().to_vec())).unwrap();
    let p = Arc::new(rustls::crypto::aws_lc_rs::default_provider());
    let mut cl = rustls::ClientConfig::builder_with_provider(p).with_safe_default_protocol_versions().unwrap().with_root_certificates(roots).with_no_client_auth();
    cl.alpn_protocols = vec![alpn.to_vec()];
    cl.enable_early_data = true;
    (s, Arc::new(cl))
}

/// A resumption with 0-RTT data: safe requests in it are answered early
/// (the handler sees `Request::early`); a POST in it gets 425 Too Early;
/// requests after the handshake are ordinary.
#[test]
fn early_data_http11() {
    let (sc, cc) = early_configs(b"http/1.1");
    let (got, c1) = talk_with(sc.clone(), cc.clone(), b"GET /a HTTP/1.1\r\nHost: x\r\n\r\n", 1 << 20);
    assert!(got.starts_with(b"HTTP/1.1 200"));
    assert!(!c1.is_early_data_accepted());
    for chunk in [1, 7, 1 << 20] {
        let early = b"GET /e HTTP/1.1\r\nHost: x\r\n\r\nPOST /p HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\n\r\nhi";
        let late = b"POST /q HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\n\r\nhi";
        let (got, c2) = talk_early(sc.clone(), cc.clone(), early, late, chunk);
        assert_eq!(c2.handshake_kind(), Some(rustls::HandshakeKind::Resumed));
        let text = String::from_utf8_lossy(&got);
        if c2.is_early_data_accepted() {
            assert!(text.contains("/e (early)"), "{chunk}: {text}");
            assert!(text.contains("HTTP/1.1 425 Too Early"), "{chunk}: {text}");
        } else {
            // Cut into single bytes, the handshake may finish before the
            // server reads the early records: then nothing is early.
            assert!(chunk < 1 << 20, "0-RTT accepted in one piece");
            assert!(text.contains("/e") && !text.contains("425"), "{chunk}: {text}");
        }
        assert!(text.contains("/q") && !text.contains("/q (early)"), "{chunk}: {text}");
    }
}

#[test]
fn early_data_h2() {
    let (sc, cc) = early_configs(b"h2");
    let preface = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n\x00\x00\x00\x04\x00\x00\x00\x00\x00";
    let (_, c1) = talk_with(sc.clone(), cc.clone(), preface, 1 << 20);
    assert!(!c1.is_early_data_accepted());
    // Over h2 the 0-RTT data is the preface, SETTINGS and requests.
    let mut early = preface.to_vec();
    // HEADERS, stream 1, END_STREAM|END_HEADERS: :method GET, :scheme
    // https, :path /, :authority x (HPACK static indexes, literal value).
    let block = [0x82, 0x87, 0x84, 0x41, 0x01, b'x'];
    early.extend_from_slice(&[0, 0, block.len() as u8, 1, 5, 0, 0, 0, 1]);
    early.extend_from_slice(&block);
    let (got, c2) = talk_early(sc, cc, &early, b"", 1 << 20);
    assert!(c2.is_early_data_accepted());
    assert!(got.windows(9).any(|w| w == b"/ (early)"), "{:?}", String::from_utf8_lossy(&got));
}

/// Encrypted Client Hello: a rustls client with the server's
/// ECHConfigList has its real ClientHello accepted, and HTTP/1.1 works
/// over the handshake.
#[test]
fn ech_http11() {
    use rustls::client::{EchConfig, EchMode, EchStatus};
    use rustls::crypto::aws_lc_rs::hpke::ALL_SUPPORTED_SUITES;
    use rustls::pki_types::EchConfigListBytes;
    use verilith_server::tls::{EchKeys, TlsOptions};
    let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
    let keys = Arc::new(EchKeys::generate(1, "localhost").unwrap());
    let opts = TlsOptions { ech: Some(keys.clone()), ..TlsOptions::default() };
    let sc = verilith_server::tls::config_der_opts(vec![c.cert.der().to_vec()], &c.signing_key.serialize_der(), &opts).unwrap();
    let mut roots = rustls::RootCertStore::empty();
    roots.add(CertificateDer::from(c.cert.der().to_vec())).unwrap();
    let mode = EchMode::Enable(EchConfig::new(EchConfigListBytes::from(keys.config_list().to_vec()), ALL_SUPPORTED_SUITES).unwrap());
    let mut cl = rustls::ClientConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_ech(mode)
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    cl.alpn_protocols = vec![b"http/1.1".to_vec()];
    for chunk in [1usize, 7, 1 << 20] {
        let (got, cli) = talk_with(sc.clone(), Arc::new(cl.clone()), b"GET /ech HTTP/1.1\r\nHost: localhost\r\n\r\n", chunk);
        assert_eq!(cli.ech_status(), EchStatus::Accepted, "{chunk}");
        assert!(String::from_utf8_lossy(&got).contains("/ech"), "{chunk}");
    }
}

#[test]
fn base64_encodes() {
    use verilith_server::tls::base64_encode as b;
    assert_eq!(b(b""), "");
    assert_eq!(b(b"f"), "Zg==");
    assert_eq!(b(b"fo"), "Zm8=");
    assert_eq!(b(b"foo"), "Zm9v");
    assert_eq!(b(b"foobar"), "Zm9vYmFy");
}
