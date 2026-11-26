//! Handshakes and data with a rustls client, in memory.
use rustls::pki_types::{CertificateDer, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore};
use std::io::{Read, Write};
use std::sync::Arc;
use verilith_tls::server::{Config, Error};
use verilith_tls::stream::ServerStream;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("data/leaf.der");
const CA: &[u8] = include_bytes!("data/ca.der");
const KEY: &[u8] = include_bytes!("data/leaf.key.der");

fn server_config(suites: &[u16], groups: &[u16], alpn: &[&[u8]]) -> Arc<Config> {
    let mut wire = Vec::new();
    for p in alpn {
        wire.push(p.len() as u8);
        wire.extend_from_slice(p);
    }
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    Arc::new(
        Config::new(suites.to_vec(), groups.to_vec(), key.schemes().to_vec(), wire, &vec![LEAF.to_vec()]).unwrap(),
    )
}

fn server(cfg: &Arc<Config>) -> ServerStream<AwsLc> {
    ServerStream::new(cfg.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())))
}

fn client_config(groups: Option<Vec<&'static dyn rustls::crypto::SupportedKxGroup>>, alpn: &[&[u8]]) -> Arc<ClientConfig> {
    let mut roots = RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    let mut provider = rustls::crypto::aws_lc_rs::default_provider();
    if let Some(g) = groups {
        provider.kx_groups = g;
    }
    let mut c = ClientConfig::builder_with_provider(Arc::new(provider))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    c.alpn_protocols = alpn.iter().map(|p| p.to_vec()).collect();
    Arc::new(c)
}

/// Moves bytes both ways until neither side has anything to say.
fn pump(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>) -> Result<(), Error> {
    pump_into(c, s, &mut Vec::new())
}

fn pump_into(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>, got: &mut Vec<u8>) -> Result<(), Error> {
    for _ in 0..20 {
        let mut buf = Vec::new();
        while c.wants_write() {
            c.write_tls(&mut buf).unwrap();
        }
        let mut moved = !buf.is_empty();
        s.read_tls(&buf);
        s.process()?;
        let out = s.take_pending();
        if !out.is_empty() {
            moved = true;
            let mut rd = &out[..];
            while !rd.is_empty() {
                c.read_tls(&mut rd).unwrap();
                c.process_new_packets().expect("client accepts what the server sends");
                let _ = c.reader().read_to_end(got);
            }
        }
        if !moved {
            return Ok(());
        }
    }
    Ok(())
}

fn handshake(cc: Arc<ClientConfig>, sc: &Arc<Config>) -> (ClientConnection, ServerStream<AwsLc>) {
    let mut c = ClientConnection::new(cc, ServerName::try_from("localhost").unwrap()).unwrap();
    let mut s = server(sc);
    pump(&mut c, &mut s).unwrap();
    assert!(!c.is_handshaking(), "client handshake done");
    assert!(!s.is_handshaking(), "server handshake done");
    (c, s)
}

fn echo(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>, n: usize) {
    let msg: Vec<u8> = (0..n).map(|i| (i * 7) as u8).collect();
    c.writer().write_all(&msg).unwrap();
    pump(c, s).unwrap();
    assert_eq!(s.plaintext(), &msg[..]);
    let l = s.plaintext().len();
    s.consume_plaintext(l);
    s.write(&msg).unwrap();
    let mut got = Vec::new();
    pump_into(c, s, &mut got).unwrap();
    assert_eq!(got, msg);
}

#[test]
fn every_suite_and_group() {
    use rustls::crypto::aws_lc_rs::kx_group;
    let groups: [(&'static dyn rustls::crypto::SupportedKxGroup, u16); 4] = [
        (kx_group::X25519, X25519),
        (kx_group::SECP256R1, SECP256R1),
        (kx_group::SECP384R1, SECP384R1),
        (kx_group::X25519MLKEM768, X25519MLKEM768),
    ];
    for suite in SUITES {
        for (g, id) in groups {
            let sc = server_config(&[suite], &[id], &[]);
            let (mut c, mut s) = handshake(client_config(Some(vec![g]), &[]), &sc);
            assert_eq!(c.negotiated_cipher_suite().unwrap().suite(), rustls::CipherSuite::from(suite));
            echo(&mut c, &mut s, 100);
            echo(&mut c, &mut s, 40000);
        }
    }
}

#[test]
fn alpn() {
    let sc = server_config(&SUITES, &GROUPS, &[b"h2", b"http/1.1"]);
    let (c, s) = handshake(client_config(None, &[b"http/1.1", b"h2"]), &sc);
    assert_eq!(c.alpn_protocol(), Some(&b"h2"[..]));
    assert_eq!(s.alpn(), Some(&b"h2"[..]));
    let (c, s) = handshake(client_config(None, &[b"http/1.1"]), &sc);
    assert_eq!(c.alpn_protocol(), Some(&b"http/1.1"[..]));
    assert_eq!(s.alpn(), Some(&b"http/1.1"[..]));
    let (c, s) = handshake(client_config(None, &[]), &sc);
    assert_eq!(c.alpn_protocol(), None);
    assert_eq!(s.alpn(), None);
}

#[test]
fn hello_retry_request() {
    use rustls::crypto::aws_lc_rs::kx_group;
    // The client's first key share is X25519; the server takes only P-256.
    let sc = server_config(&SUITES, &[SECP256R1], &[]);
    let (mut c, mut s) = handshake(client_config(Some(vec![kx_group::X25519, kx_group::SECP256R1]), &[]), &sc);
    assert_eq!(c.negotiated_key_exchange_group().unwrap().name(), rustls::NamedGroup::secp256r1);
    echo(&mut c, &mut s, 1000);
}

#[test]
fn key_update_and_close() {
    let sc = server_config(&SUITES, &GROUPS, &[]);
    let (mut c, mut s) = handshake(client_config(None, &[]), &sc);
    for _ in 0..3 {
        c.refresh_traffic_keys().unwrap();
        echo(&mut c, &mut s, 500);
    }
    c.send_close_notify();
    pump(&mut c, &mut s).unwrap();
    assert!(s.peer_closed());
}

#[test]
fn no_common_group_or_alpn() {
    use rustls::crypto::aws_lc_rs::kx_group;
    let sc = server_config(&SUITES, &[SECP384R1], &[]);
    let mut c = ClientConnection::new(client_config(Some(vec![kx_group::X25519]), &[]), ServerName::try_from("localhost").unwrap()).unwrap();
    let mut s = server(&sc);
    let mut buf = Vec::new();
    c.write_tls(&mut buf).unwrap();
    s.read_tls(&buf);
    assert_eq!(s.process(), Err(Error::Sent(40)));
    let sc = server_config(&SUITES, &GROUPS, &[b"h2"]);
    let mut c = ClientConnection::new(client_config(None, &[b"spdy"]), ServerName::try_from("localhost").unwrap()).unwrap();
    let mut s = server(&sc);
    let mut buf = Vec::new();
    c.write_tls(&mut buf).unwrap();
    s.read_tls(&buf);
    assert_eq!(s.process(), Err(Error::Sent(120)));
}

#[test]
fn byte_at_a_time() {
    let sc = server_config(&SUITES, &GROUPS, &[]);
    let mut c = ClientConnection::new(client_config(None, &[]), ServerName::try_from("localhost").unwrap()).unwrap();
    let mut s = server(&sc);
    for _ in 0..10 {
        let mut buf = Vec::new();
        while c.wants_write() {
            c.write_tls(&mut buf).unwrap();
        }
        for b in &buf {
            s.read_tls(std::slice::from_ref(b));
            s.process().unwrap();
        }
        let out = s.take_pending();
        let mut rd = &out[..];
        while !rd.is_empty() {
            c.read_tls(&mut rd).unwrap();
            c.process_new_packets().unwrap();
        }
    }
    assert!(!c.is_handshaking() && !s.is_handshaking());
    echo(&mut c, &mut s, 3000);
}

#[test]
fn tampered_records_are_refused() {
    let sc = server_config(&SUITES, &GROUPS, &[]);
    let (mut c, mut s) = handshake(client_config(None, &[]), &sc);
    c.writer().write_all(b"hello").unwrap();
    let mut buf = Vec::new();
    c.write_tls(&mut buf).unwrap();
    let last = buf.len() - 1;
    buf[last] ^= 1;
    s.read_tls(&buf);
    assert_eq!(s.process(), Err(Error::Sent(20)));
    assert_eq!(s.write(b"x"), Err(Error::Closed));
}
