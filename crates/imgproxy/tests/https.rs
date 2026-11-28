//! `https://` sources end to end (`--features tls`): an origin served by
//! verilith-server's TLS on localhost, with a certificate made here, and
//! the proxy fetching from it through the verified TLS client.
#![cfg(feature = "tls")]
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, OnceLock};
use std::time::Duration;
use verilith_imgproxy::handler::Proxy;
use verilith_imgproxy::proxy::{self, Fail, Keys, Limits};
use verilith_server::{serve, Config, Field, Request, Response};

fn png(w: u32, h: u32) -> Vec<u8> {
    let img = image::RgbImage::from_fn(w, h, |x, y| image::Rgb([(x * 4) as u8, (y * 4) as u8, 128]));
    let mut out = std::io::Cursor::new(Vec::new());
    img.write_to(&mut out, image::ImageFormat::Png).unwrap();
    out.into_inner()
}

/// The origin's TLS port and its certificate (DER).
fn origin() -> &'static (u16, Vec<u8>) {
    static S: OnceLock<(u16, Vec<u8>)> = OnceLock::new();
    S.get_or_init(|| {
        let c = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
        let der = c.cert.der().to_vec();
        let tls = verilith_server::tls::config_der(vec![der.clone()], &c.signing_key.serialize_der()).unwrap();
        let port = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let http = TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
        let img = png(64, 48);
        let h = move |req: &Request, res: &mut Response| {
            let _ = match req.path() {
                b"/img.png" => res.send(200, &[Field { name: b"Content-Type", value: b"image/png" }], &img),
                _ => res.send(404, &[], b"no"),
            };
        };
        let cfg = Config { port: http, threads: 2, pin: false, tls: Some((port, tls)), ..Config::default() };
        std::thread::spawn(move || serve(cfg, Arc::new(h)));
        for _ in 0..500 {
            if TcpStream::connect(("127.0.0.1", port)).is_ok() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        (port, der)
    })
}

fn proxy_trusting(roots: Vec<Vec<u8>>) -> Proxy {
    Proxy {
        keys: Keys { key: Vec::new(), salt: Vec::new() },
        limits: Limits::default(),
        local_root: None,
        http_sources: true,
        tls: Some(proxy::tls_config(roots)),
        allowed: Vec::new(),
        ttl: 60,
    }
}

#[test]
fn fetches_https_source() {
    let (port, der) = origin().clone();
    let p = proxy_trusting(vec![der]);
    let out = p.answer(b"GET", format!("/x/rs:fit:16:16/plain/https://localhost:{port}/img.png").as_bytes(), b"").unwrap().body;
    let d = png::Decoder::new(std::io::Cursor::new(out)).read_info().unwrap();
    assert_eq!((d.info().width, d.info().height), (16, 12));
    assert_eq!(
        p.answer(b"GET", format!("/x/plain/https://localhost:{port}/missing.png").as_bytes(), b""),
        Err(Fail::NotFound)
    );
}

#[test]
fn refuses_untrusted_origin() {
    let (port, _) = origin().clone();
    let other = rcgen::generate_simple_self_signed(vec!["localhost".to_string()]).unwrap();
    let p = proxy_trusting(vec![other.cert.der().to_vec()]);
    let r = p.answer(b"GET", format!("/x/plain/https://localhost:{port}/img.png").as_bytes(), b"");
    assert_eq!(r, Err(Fail::BadGateway("TLS handshake with origin failed")));
}

#[test]
fn refuses_ip_hosts_and_missing_tls() {
    let (port, der) = origin().clone();
    let p = proxy_trusting(vec![der]);
    let r = p.answer(b"GET", format!("/x/plain/https://127.0.0.1:{port}/img.png").as_bytes(), b"");
    assert_eq!(r, Err(Fail::BadUrl("https sources need a host name, not an IP address")));
    let mut q = proxy_trusting(Vec::new());
    q.tls = None;
    let r = q.answer(b"GET", format!("/x/plain/https://localhost:{port}/img.png").as_bytes(), b"");
    assert_eq!(r, Err(Fail::BadUrl("https sources are not enabled")));
}

#[test]
fn reads_pem_bundles() {
    let (_, der) = origin().clone();
    let b64 = verilith_text::base64::STANDARD.encode(&der);
    let mut pem = String::from("junk\n-----BEGIN CERTIFICATE-----\n");
    for l in b64.as_bytes().chunks(64) {
        pem.push_str(std::str::from_utf8(l).unwrap());
        pem.push('\n');
    }
    pem.push_str("-----END CERTIFICATE-----\n");
    assert_eq!(proxy::pem_certs(pem.as_bytes()), vec![der]);
}
