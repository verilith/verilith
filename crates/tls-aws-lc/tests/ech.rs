//! Encrypted Client Hello (RFC 9849) with rustls's ECH client, in memory:
//! accepted (the handshake is ClientHelloInner's), declined with
//! retry_configs when the keys differ, GREASE, resumption and 0-RTT under
//! ECH.
use rustls::client::{EchConfig, EchGreaseConfig, EchMode, EchStatus};
use rustls::crypto::aws_lc_rs::hpke::ALL_SUPPORTED_SUITES;
use rustls::pki_types::{CertificateDer, EchConfigListBytes, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore};
use std::io::{Read, Write};
use std::sync::Arc;
use verilith_tls::server::Config;
use verilith_tls::stream::ServerStream;
use verilith_tls_aws_lc::hpke::EchKeys;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("data/leaf.der");
const CA: &[u8] = include_bytes!("data/ca.der");
const KEY: &[u8] = include_bytes!("data/leaf.key.der");

/// The leaf is valid for localhost (the inner name) and example.com
/// (the public name).
const PUBLIC: &str = "example.com";

fn server_config(ech: &EchKeys) -> Arc<Config> {
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    let mut c = Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), b"\x02h2".to_vec(), &vec![LEAF.to_vec()]).unwrap();
    c.set_tickets(2, 3600);
    c.set_early_data(16384);
    assert!(c.set_ech(ech.config_list().to_vec()));
    Arc::new(c)
}

fn server(cfg: &Arc<Config>, ech: &Arc<EchKeys>, tickets: &Arc<TicketKeys>) -> ServerStream<AwsLc> {
    ServerStream::new(cfg.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())).with_tickets(tickets.clone()).with_ech(ech.clone()))
}

fn client_config(mode: EchMode) -> Arc<ClientConfig> {
    let mut roots = RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    let mut c = ClientConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_ech(mode)
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    c.alpn_protocols = vec![b"h2".to_vec()];
    c.enable_early_data = true;
    Arc::new(c)
}

fn enable(list: &[u8]) -> EchMode {
    EchMode::Enable(EchConfig::new(EchConfigListBytes::from(list.to_vec()), ALL_SUPPORTED_SUITES).unwrap())
}

fn pump(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>, got: &mut Vec<u8>) -> Result<(), rustls::Error> {
    for _ in 0..20 {
        let mut buf = Vec::new();
        while c.wants_write() {
            c.write_tls(&mut buf).unwrap();
        }
        s.read_tls(&buf);
        let _ = s.process();
        let out = s.take_pending();
        let moved = !buf.is_empty() || !out.is_empty();
        let mut rd = &out[..];
        while !rd.is_empty() {
            c.read_tls(&mut rd).unwrap();
            c.process_new_packets()?;
            let _ = c.reader().read_to_end(got);
        }
        if !moved {
            return Ok(());
        }
    }
    Ok(())
}

fn connect(cc: &Arc<ClientConfig>, s: &mut ServerStream<AwsLc>) -> (ClientConnection, Result<(), rustls::Error>) {
    let mut c = ClientConnection::new(cc.clone(), ServerName::try_from("localhost").unwrap()).unwrap();
    let r = pump(&mut c, s, &mut Vec::new());
    (c, r)
}

#[test]
fn ech_is_accepted() {
    let ech = Arc::new(EchKeys::generate(7, PUBLIC).unwrap());
    let tickets = Arc::new(TicketKeys::new(3600));
    let sc = server_config(&ech);
    let cc = client_config(enable(ech.config_list()));
    for _ in 0..3 {
        let mut s = server(&sc, &ech, &tickets);
        let (mut c, r) = connect(&cc, &mut s);
        r.unwrap();
        assert_eq!(c.ech_status(), EchStatus::Accepted);
        assert!(!c.is_handshaking() && !s.is_handshaking());
        assert_eq!(s.alpn(), Some(&b"h2"[..]));
        c.writer().write_all(b"inner").unwrap();
        pump(&mut c, &mut s, &mut Vec::new()).unwrap();
        assert_eq!(s.plaintext(), b"inner");
        s.consume_plaintext(5);
        s.write(b"back").unwrap();
        let mut got = Vec::new();
        pump(&mut c, &mut s, &mut got).unwrap();
        assert_eq!(got, b"back");
    }
}

#[test]
fn ech_resumes_with_early_data() {
    let ech = Arc::new(EchKeys::generate(1, PUBLIC).unwrap());
    let tickets = Arc::new(TicketKeys::new(3600));
    let sc = server_config(&ech);
    let cc = client_config(enable(ech.config_list()));
    let mut s = server(&sc, &ech, &tickets);
    let (c, r) = connect(&cc, &mut s);
    r.unwrap();
    assert_eq!(c.handshake_kind(), Some(rustls::HandshakeKind::Full));
    let mut c = ClientConnection::new(cc.clone(), ServerName::try_from("localhost").unwrap()).unwrap();
    c.early_data().expect("0-RTT under ECH").write_all(b"early").unwrap();
    let mut s = server(&sc, &ech, &tickets);
    pump(&mut c, &mut s, &mut Vec::new()).unwrap();
    assert_eq!(c.ech_status(), EchStatus::Accepted);
    assert_eq!(c.handshake_kind(), Some(rustls::HandshakeKind::Resumed));
    assert!(c.is_early_data_accepted());
    assert_eq!(s.plaintext(), b"early");
}

#[test]
fn other_keys_decline_with_retry_configs() {
    let ours = Arc::new(EchKeys::generate(3, PUBLIC).unwrap());
    let theirs = EchKeys::generate(3, PUBLIC).unwrap();
    let tickets = Arc::new(TicketKeys::new(3600));
    let sc = server_config(&ours);
    // The client has a stale config: the server cannot open it, does the
    // handshake on ClientHelloOuter (public name) and sends its own list.
    let cc = client_config(enable(theirs.config_list()));
    let mut s = server(&sc, &ours, &tickets);
    let (c, r) = connect(&cc, &mut s);
    assert_eq!(c.ech_status(), EchStatus::Rejected);
    match r {
        Err(rustls::Error::PeerIncompatible(rustls::PeerIncompatible::ServerRejectedEncryptedClientHello(Some(cfgs)))) => {
            assert_eq!(cfgs.len(), 1)
        }
        other => panic!("expected a rejection with retry configs, got {other:?}"),
    }
}

#[test]
fn grease_is_a_plain_handshake() {
    let ech = Arc::new(EchKeys::generate(9, PUBLIC).unwrap());
    let tickets = Arc::new(TicketKeys::new(3600));
    let sc = server_config(&ech);
    let suite = rustls::crypto::aws_lc_rs::hpke::DH_KEM_X25519_HKDF_SHA256_AES_128;
    let placeholder = rustls::crypto::hpke::HpkePublicKey(verilith_tls_aws_lc::hpke::HpkeKey::generate().unwrap().public().to_vec());
    let cc = client_config(EchMode::Grease(EchGreaseConfig::new(suite, placeholder)));
    let mut s = server(&sc, &ech, &tickets);
    let (c, r) = connect(&cc, &mut s);
    r.unwrap();
    assert_eq!(c.ech_status(), EchStatus::Grease);
    assert!(!c.is_handshaking() && !s.is_handshaking());
}

#[test]
fn malformed_ech_is_refused() {
    // An outer ClientHello whose encrypted_client_hello is cut short:
    // decode_error, from the verified parser.
    let ech = Arc::new(EchKeys::generate(2, PUBLIC).unwrap());
    let tickets = Arc::new(TicketKeys::new(3600));
    let sc = server_config(&ech);
    let cc = client_config(enable(ech.config_list()));
    let mut c = ClientConnection::new(cc, ServerName::try_from("localhost").unwrap()).unwrap();
    let mut ch = Vec::new();
    while c.wants_write() {
        c.write_tls(&mut ch).unwrap();
    }
    // Find the extension (type fe0d) and shorten its payload length.
    let at = ch.windows(2).position(|w| w == [0xfe, 0x0d]).unwrap();
    let ty = at + 4;
    assert_eq!(ch[ty], 0, "outer type");
    ch[ty] = 1; // an inner ECHClientHello in ClientHelloOuter
    let mut s = server(&sc, &ech, &tickets);
    s.read_tls(&ch);
    assert!(s.process().is_err());
}
