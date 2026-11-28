//! The verified client (`ClientStream`) against a rustls server, in memory.
use rcgen::{BasicConstraints, CertificateParams, DnType, IsCa, KeyPair, KeyUsagePurpose, SanType};
use rustls::crypto::SupportedKxGroup;
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
use rustls::server::WebPkiClientVerifier;
use rustls::{RootCertStore, ServerConfig, ServerConnection};
use std::io::{Read, Write};
use std::sync::Arc;
use verilith_tls::client_hs::ClientConfig;
use verilith_tls::server::Error;
use verilith_tls::stream::ClientStream;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("data/leaf.der");
const CA: &[u8] = include_bytes!("data/ca.der");
const KEY: &[u8] = include_bytes!("data/leaf.key.der");

const SIGS: [u16; 6] = [0x0403, 0x0503, 0x0807, 0x0804, 0x0805, 0x0806];

fn config(suites: &[u16], groups: &[u16], shares: usize, alpn: &[&[u8]], roots: Vec<Vec<u8>>) -> Arc<ClientConfig> {
    Arc::new(ClientConfig {
        suites: suites.to_vec(),
        groups: groups.to_vec(),
        shares,
        sigs: SIGS.to_vec(),
        alpn: alpn.iter().map(|p| p.to_vec()).collect(),
        roots,
    })
}

fn default_config() -> Arc<ClientConfig> {
    config(&SUITES, &GROUPS, 2, &[], vec![CA.to_vec()])
}

fn provider(
    suites: Option<&[u16]>,
    groups: Option<Vec<&'static dyn SupportedKxGroup>>,
) -> rustls::crypto::CryptoProvider {
    let mut p = rustls::crypto::aws_lc_rs::default_provider();
    if let Some(s) = suites {
        p.cipher_suites.retain(|c| s.contains(&u16::from(c.suite())));
    }
    if let Some(g) = groups {
        p.kx_groups = g;
    }
    p
}

fn rustls_server(
    p: rustls::crypto::CryptoProvider,
    chain: Vec<Vec<u8>>,
    key: Vec<u8>,
    alpn: &[&[u8]],
    client_auth: bool,
) -> ServerConnection {
    let p = Arc::new(p);
    let b = ServerConfig::builder_with_provider(p.clone()).with_protocol_versions(&[&rustls::version::TLS13]).unwrap();
    let b = if client_auth {
        let mut roots = RootCertStore::empty();
        roots.add(CertificateDer::from(CA.to_vec())).unwrap();
        let v = WebPkiClientVerifier::builder_with_provider(Arc::new(roots), p).allow_unauthenticated().build().unwrap();
        b.with_client_cert_verifier(v)
    } else {
        b.with_no_client_auth()
    };
    let chain = chain.into_iter().map(CertificateDer::from).collect();
    let mut c = b.with_single_cert(chain, PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key))).unwrap();
    c.alpn_protocols = alpn.iter().map(|p| p.to_vec()).collect();
    c.send_tls13_tickets = 2;
    ServerConnection::new(Arc::new(c)).unwrap()
}

fn default_server() -> ServerConnection {
    rustls_server(provider(None, None), vec![LEAF.to_vec()], KEY.to_vec(), &[], false)
}

fn client(cfg: Arc<ClientConfig>, host: &str) -> ClientStream<AwsLc> {
    ClientStream::new(cfg, host.as_bytes(), AwsLc::new(None)).expect("client starts")
}

/// Moves bytes both ways until neither side has anything to say. Returns
/// the client's error, or the server's, and what the client read.
fn pump(c: &mut ClientStream<AwsLc>, s: &mut ServerConnection, tamper: &mut dyn FnMut(&mut Vec<u8>)) -> Result<Vec<u8>, String> {
    let mut got_s = Vec::new();
    for _ in 0..30 {
        let out = c.take_pending();
        let mut moved = !out.is_empty();
        let mut rd = &out[..];
        while !rd.is_empty() {
            s.read_tls(&mut rd).unwrap();
            s.process_new_packets().map_err(|e| format!("server: {e:?}"))?;
            let _ = s.reader().read_to_end(&mut got_s);
        }
        let mut buf = Vec::new();
        while s.wants_write() {
            s.write_tls(&mut buf).unwrap();
        }
        if !buf.is_empty() {
            moved = true;
            tamper(&mut buf);
            c.read_tls(&buf);
            if let Err(e) = c.process() {
                return Err(format!("client: {e:?}"));
            }
        }
        if !moved {
            break;
        }
    }
    Ok(got_s)
}

fn connect(c: &mut ClientStream<AwsLc>, s: &mut ServerConnection) -> Result<(), String> {
    pump(c, s, &mut |_| {})?;
    if c.is_handshaking() {
        return Err("client still handshaking".into());
    }
    Ok(())
}

/// Data both ways after the handshake, bigger than a record.
fn exchange(c: &mut ClientStream<AwsLc>, s: &mut ServerConnection) {
    let up: Vec<u8> = (0..40_000u32).map(|i| (i * 7) as u8).collect();
    let down: Vec<u8> = (0..50_000u32).map(|i| (i * 13) as u8).collect();
    c.write(&up).unwrap();
    s.writer().write_all(&down).unwrap();
    let got = pump(c, s, &mut |_| {}).unwrap();
    assert_eq!(got, up);
    assert_eq!(c.plaintext(), &down[..]);
    let n = c.plaintext().len();
    c.consume_plaintext(n);
}

#[test]
fn every_suite_and_group() {
    let groups: [(u16, &'static dyn SupportedKxGroup); 4] = [
        (X25519MLKEM768, rustls::crypto::aws_lc_rs::kx_group::X25519MLKEM768),
        (X25519, rustls::crypto::aws_lc_rs::kx_group::X25519),
        (SECP256R1, rustls::crypto::aws_lc_rs::kx_group::SECP256R1),
        (SECP384R1, rustls::crypto::aws_lc_rs::kx_group::SECP384R1),
    ];
    for suite in SUITES {
        for (g, rg) in groups {
            let mut s = rustls_server(provider(Some(&[suite]), Some(vec![rg])), vec![LEAF.to_vec()], KEY.to_vec(), &[], false);
            // The client's share is for exactly the server's group.
            let mut c = client(config(&SUITES, &[g], 1, &[], vec![CA.to_vec()]), "localhost");
            connect(&mut c, &mut s).unwrap_or_else(|e| panic!("suite {suite:#x} group {g:#x}: {e}"));
            assert_eq!(s.negotiated_cipher_suite().map(|c| u16::from(c.suite())), Some(suite));
            exchange(&mut c, &mut s);
        }
    }
}

#[test]
fn default_handshake_and_names() {
    for host in ["localhost", "LocalHost", "example.com"] {
        let mut s = default_server();
        let mut c = client(default_config(), host);
        connect(&mut c, &mut s).unwrap();
        assert_eq!(s.server_name().map(|n| n.to_ascii_lowercase()), Some(host.to_ascii_lowercase()));
        assert_eq!(c.peer_certificates(), &[LEAF.to_vec()]);
        assert_eq!(c.alpn(), None);
        exchange(&mut c, &mut s);
    }
}

#[test]
fn hello_retry_request() {
    // The client's one share is X25519; the server takes only P-384.
    let mut s = rustls_server(
        provider(None, Some(vec![rustls::crypto::aws_lc_rs::kx_group::SECP384R1])),
        vec![LEAF.to_vec()],
        KEY.to_vec(),
        &[],
        false,
    );
    let mut c = client(config(&SUITES, &[X25519, SECP256R1, SECP384R1], 1, &[], vec![CA.to_vec()]), "localhost");
    connect(&mut c, &mut s).unwrap();
    assert_eq!(s.negotiated_key_exchange_group().map(|g| u16::from(g.name())), Some(SECP384R1));
    exchange(&mut c, &mut s);
}

#[test]
fn hello_retry_request_hybrid() {
    let mut s = rustls_server(
        provider(None, Some(vec![rustls::crypto::aws_lc_rs::kx_group::X25519MLKEM768])),
        vec![LEAF.to_vec()],
        KEY.to_vec(),
        &[],
        false,
    );
    let mut c = client(config(&SUITES, &[X25519, X25519MLKEM768], 1, &[], vec![CA.to_vec()]), "localhost");
    connect(&mut c, &mut s).unwrap();
    exchange(&mut c, &mut s);
}

#[test]
fn no_common_group() {
    let mut s = rustls_server(
        provider(None, Some(vec![rustls::crypto::aws_lc_rs::kx_group::SECP384R1])),
        vec![LEAF.to_vec()],
        KEY.to_vec(),
        &[],
        false,
    );
    let mut c = client(config(&SUITES, &[X25519], 1, &[], vec![CA.to_vec()]), "localhost");
    assert!(connect(&mut c, &mut s).is_err());
}

#[test]
fn alpn() {
    let mut s = rustls_server(provider(None, None), vec![LEAF.to_vec()], KEY.to_vec(), &[b"h2", b"http/1.1"], false);
    let mut c = client(config(&SUITES, &GROUPS, 2, &[b"http/1.1", b"h2"], vec![CA.to_vec()]), "localhost");
    connect(&mut c, &mut s).unwrap();
    assert_eq!(c.alpn(), Some(&b"h2"[..]));
    assert_eq!(s.alpn_protocol(), Some(&b"h2"[..]));
    exchange(&mut c, &mut s);
}

#[test]
fn alpn_server_has_none_in_common() {
    // rustls refuses with no_application_protocol.
    let mut s = rustls_server(provider(None, None), vec![LEAF.to_vec()], KEY.to_vec(), &[b"h2"], false);
    let mut c = client(config(&SUITES, &GROUPS, 2, &[b"http/1.1"], vec![CA.to_vec()]), "localhost");
    assert!(connect(&mut c, &mut s).is_err());
}

#[test]
fn key_update_from_server() {
    let mut s = default_server();
    let mut c = client(default_config(), "localhost");
    connect(&mut c, &mut s).unwrap();
    for _ in 0..3 {
        s.refresh_traffic_keys().unwrap();
        exchange(&mut c, &mut s);
    }
}

#[test]
fn certificate_request_gets_empty_certificate() {
    let mut s = rustls_server(provider(None, None), vec![LEAF.to_vec()], KEY.to_vec(), &[], true);
    let mut c = client(default_config(), "localhost");
    connect(&mut c, &mut s).unwrap();
    assert!(s.peer_certificates().is_none());
    exchange(&mut c, &mut s);
}

#[test]
fn wrong_host_name() {
    let mut s = default_server();
    let mut c = client(default_config(), "example.org");
    let e = connect(&mut c, &mut s).unwrap_err();
    assert!(e.contains("Sent(42)"), "{e}");
}

#[test]
fn unknown_ca() {
    let other = ca("other CA");
    let mut s = default_server();
    let mut c = client(config(&SUITES, &GROUPS, 2, &[], vec![other.der.clone()]), "localhost");
    let e = connect(&mut c, &mut s).unwrap_err();
    assert!(e.contains("Sent(48)"), "{e}");
}

#[test]
fn tampered_flight() {
    let mut s = default_server();
    let mut c = client(default_config(), "localhost");
    let mut first = true;
    let e = pump(&mut c, &mut s, &mut |b: &mut Vec<u8>| {
        if first {
            first = false;
            let n = b.len();
            b[n - 3] ^= 1;
        }
    })
    .unwrap_err();
    assert!(e.contains("Sent(20)"), "{e}");
}

#[test]
fn server_close_notify() {
    let mut s = default_server();
    let mut c = client(default_config(), "localhost");
    connect(&mut c, &mut s).unwrap();
    s.send_close_notify();
    pump(&mut c, &mut s, &mut |_| {}).unwrap();
    assert!(c.peer_closed());
    assert!(matches!(c.write(b"x"), Ok(()) | Err(Error::Closed)));
}

#[test]
fn client_close_notify() {
    let mut s = default_server();
    let mut c = client(default_config(), "localhost");
    connect(&mut c, &mut s).unwrap();
    c.close();
    pump(&mut c, &mut s, &mut |_| {}).unwrap();
    let mut buf = [0u8; 1];
    assert_eq!(s.reader().read(&mut buf).unwrap(), 0);
    assert!(matches!(c.write(b"x"), Err(Error::Closed)));
}

#[test]
fn bad_inputs() {
    assert!(ClientStream::new(default_config(), b"", AwsLc::new(None)).is_none());
    assert!(ClientStream::new(default_config(), b"127.0.0.1", AwsLc::new(None)).is_none());
    assert!(ClientStream::new(default_config(), b"a..b", AwsLc::new(None)).is_none());
    assert!(ClientStream::new(config(&[0x1304], &GROUPS, 1, &[], vec![]), b"a.b", AwsLc::new(None)).is_none());
    assert!(ClientStream::new(config(&SUITES, &[], 1, &[], vec![]), b"a.b", AwsLc::new(None)).is_none());
}

// -- chains made with rcgen -------------------------------------------------

struct Ca {
    params: CertificateParams,
    key: KeyPair,
    der: Vec<u8>,
}

fn ca(name: &str) -> Ca {
    let key = KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256).unwrap();
    let mut params = CertificateParams::new(Vec::<String>::new()).unwrap();
    params.distinguished_name.push(DnType::CommonName, name);
    params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    params.key_usages = vec![KeyUsagePurpose::KeyCertSign, KeyUsagePurpose::CrlSign];
    let cert = params.clone().self_signed(&key).unwrap();
    Ca { params, key, der: cert.der().to_vec() }
}

fn sub_ca(name: &str, issuer: &Ca, edit: impl FnOnce(&mut CertificateParams)) -> Ca {
    let key = KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256).unwrap();
    let mut params = CertificateParams::new(Vec::<String>::new()).unwrap();
    params.distinguished_name.push(DnType::CommonName, name);
    params.is_ca = IsCa::Ca(BasicConstraints::Constrained(0));
    params.key_usages = vec![KeyUsagePurpose::KeyCertSign];
    edit(&mut params);
    let issuer_cert = issuer.params.clone().self_signed(&issuer.key).unwrap();
    let cert = params.clone().signed_by(&key, &issuer_cert, &issuer.key).unwrap();
    Ca { params, key, der: cert.der().to_vec() }
}

fn server_leaf(issuer: &Ca, names: &[&str], edit: impl FnOnce(&mut CertificateParams)) -> (Vec<u8>, Vec<u8>) {
    let key = KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256).unwrap();
    let mut params = CertificateParams::new(names.iter().map(|s| s.to_string()).collect::<Vec<_>>()).unwrap();
    params.distinguished_name.push(DnType::CommonName, "server");
    params.key_usages = vec![KeyUsagePurpose::DigitalSignature];
    params.extended_key_usages = vec![rcgen::ExtendedKeyUsagePurpose::ServerAuth];
    edit(&mut params);
    let issuer_cert = issuer.params.clone().self_signed(&issuer.key).unwrap();
    let cert = params.signed_by(&key, &issuer_cert, &issuer.key).unwrap();
    (cert.der().to_vec(), key.serialize_der())
}

/// Whether the client connects to `host` through `chain` with `root`.
fn try_chain(root: &Ca, chain: Vec<Vec<u8>>, key: Vec<u8>, host: &str) -> Result<(), String> {
    // rustls checks its own chain only against its key, so it serves any.
    let mut s = rustls_server(provider(None, None), chain, key, &[], false);
    let mut c = client(config(&SUITES, &GROUPS, 2, &[], vec![root.der.clone()]), host);
    connect(&mut c, &mut s).inspect_err(|e| eprintln!("{host}: {e}"))?;
    exchange(&mut c, &mut s);
    Ok(())
}

#[test]
fn intermediate_chain() {
    let root = ca("root");
    let mid = sub_ca("mid", &root, |_| {});
    let (leaf, key) = server_leaf(&mid, &["www.example.net"], |_| {});
    try_chain(&root, vec![leaf.clone(), mid.der.clone()], key.clone(), "www.example.net").unwrap();
    // Without the intermediate there is no path.
    assert!(try_chain(&root, vec![leaf.clone()], key.clone(), "www.example.net").unwrap_err().contains("Sent(48)"));
    // Anything after the path is ignored.
    try_chain(&root, vec![leaf, mid.der.clone(), root.der.clone(), b"junk".to_vec()], key, "www.example.net").unwrap();
}

#[test]
fn wildcards() {
    let root = ca("root");
    let (leaf, key) = server_leaf(&root, &["*.example.net"], |_| {});
    for (host, ok) in [
        ("a.example.net", true),
        ("A.Example.NET", true),
        ("example.net", false),
        ("a.b.example.net", false),
        ("aexample.net", false),
    ] {
        let r = try_chain(&root, vec![leaf.clone()], key.clone(), host);
        assert_eq!(r.is_ok(), ok, "{host}: {r:?}");
    }
    // A wildcard needs two labels after it.
    let (leaf, key) = server_leaf(&root, &["*.net"], |_| {});
    assert!(try_chain(&root, vec![leaf], key, "example.net").is_err());
}

#[test]
fn name_constraints() {
    let root = ca("root");
    let mid = sub_ca("mid", &root, |p| {
        p.name_constraints = Some(rcgen::NameConstraints {
            permitted_subtrees: vec![rcgen::GeneralSubtree::DnsName("example.net".into())],
            excluded_subtrees: vec![rcgen::GeneralSubtree::DnsName("bad.example.net".into())],
        });
    });
    for (host, ok) in [("example.net", true), ("www.example.net", true), ("bad.example.net", false), ("x.bad.example.net", false), ("example.org", false)] {
        let (leaf, key) = server_leaf(&mid, &[host], |_| {});
        let r = try_chain(&root, vec![leaf, mid.der.clone()], key, host);
        assert_eq!(r.is_ok(), ok, "{host}: {r:?}");
    }
}

#[test]
fn leaf_rules() {
    let root = ca("root");
    // Expired.
    let (leaf, key) = server_leaf(&root, &["a.test"], |p| {
        p.not_before = rcgen::date_time_ymd(2001, 1, 1);
        p.not_after = rcgen::date_time_ymd(2002, 1, 1);
    });
    assert!(try_chain(&root, vec![leaf], key, "a.test").is_err());
    // For clients only.
    let (leaf, key) = server_leaf(&root, &["a.test"], |p| p.extended_key_usages = vec![rcgen::ExtendedKeyUsagePurpose::ClientAuth]);
    assert!(try_chain(&root, vec![leaf], key, "a.test").is_err());
    // A CA as the leaf.
    let (leaf, key) = server_leaf(&root, &["a.test"], |p| p.is_ca = IsCa::Ca(BasicConstraints::Unconstrained));
    assert!(try_chain(&root, vec![leaf], key, "a.test").is_err());
    // Only the subject's CN names the host: no fallback.
    let (leaf, key) = server_leaf(&root, &[], |p| {
        p.distinguished_name = rcgen::DistinguishedName::new();
        p.distinguished_name.push(DnType::CommonName, "a.test");
    });
    assert!(try_chain(&root, vec![leaf], key, "a.test").is_err());
    // An IP address SAN does not name a DNS host.
    let (leaf, key) = server_leaf(&root, &[], |p| p.subject_alt_names = vec![SanType::IpAddress("10.0.0.1".parse().unwrap())]);
    assert!(try_chain(&root, vec![leaf], key, "a.test").is_err());
}

#[test]
fn intermediate_must_be_ca() {
    let root = ca("root");
    let (not_ca, not_ca_key) = server_leaf(&root, &["mid.test"], |_| {});
    // Sign a leaf with a non-CA certificate's key.
    let mid_key = KeyPair::try_from(not_ca_key.as_slice()).unwrap();
    let mut mid_params = CertificateParams::new(vec!["mid.test".to_string()]).unwrap();
    mid_params.distinguished_name.push(DnType::CommonName, "server");
    let mid_cert = mid_params.self_signed(&mid_key).unwrap();
    let key = KeyPair::generate_for(&rcgen::PKCS_ECDSA_P256_SHA256).unwrap();
    let leaf = CertificateParams::new(vec!["a.test".to_string()]).unwrap().signed_by(&key, &mid_cert, &mid_key).unwrap();
    assert!(try_chain(&root, vec![leaf.der().to_vec(), not_ca], key.serialize_der(), "a.test").is_err());
}
