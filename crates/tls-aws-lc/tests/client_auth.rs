//! Client authentication (mutual TLS) with a rustls client, in memory.
use rcgen::{
    BasicConstraints, CertificateParams, DnType, ExtendedKeyUsagePurpose, IsCa, KeyPair, KeyUsagePurpose,
    SignatureAlgorithm, PKCS_ECDSA_P256_SHA256, PKCS_ECDSA_P384_SHA384, PKCS_ED25519,
};
use rustls::client::danger::{ServerCertVerified, ServerCertVerifier, HandshakeSignatureValid};
use rustls::client::{ClientSessionMemoryCache, ResolvesClientCert, Resumption};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer, ServerName, UnixTime};
use rustls::sign::CertifiedKey;
use rustls::{ClientConfig, ClientConnection, DigitallySignedStruct, HandshakeKind, RootCertStore, SignatureScheme};
use std::io::{Read, Write};
use std::sync::Arc;
use verilith_tls::server::{Config, Error};
use verilith_tls::stream::ServerStream;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("data/leaf.der");
const CA: &[u8] = include_bytes!("data/ca.der");
const KEY: &[u8] = include_bytes!("data/leaf.key.der");

const CLIENT_SIGS: [u16; 6] = [0x0403, 0x0503, 0x0807, 0x0804, 0x0805, 0x0806];

/// A CA, its key, and its DER certificate.
struct Ca {
    params: CertificateParams,
    key: KeyPair,
    der: Vec<u8>,
}

fn ca(name: &str, alg: &'static SignatureAlgorithm) -> Ca {
    let key = KeyPair::generate_for(alg).unwrap();
    let mut params = CertificateParams::new(Vec::<String>::new()).unwrap();
    params.distinguished_name.push(DnType::CommonName, name);
    params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    params.key_usages = vec![KeyUsagePurpose::KeyCertSign, KeyUsagePurpose::CrlSign];
    let cert = params.clone().self_signed(&key).unwrap();
    Ca { params, key, der: cert.der().to_vec() }
}

fn intermediate(name: &str, issuer: &Ca, alg: &'static SignatureAlgorithm) -> Ca {
    let key = KeyPair::generate_for(alg).unwrap();
    let mut params = CertificateParams::new(Vec::<String>::new()).unwrap();
    params.distinguished_name.push(DnType::CommonName, name);
    params.is_ca = IsCa::Ca(BasicConstraints::Constrained(0));
    params.key_usages = vec![KeyUsagePurpose::KeyCertSign];
    let issuer_cert = issuer.params.clone().self_signed(&issuer.key).unwrap();
    let cert = params.clone().signed_by(&key, &issuer_cert, &issuer.key).unwrap();
    Ca { params, key, der: cert.der().to_vec() }
}

/// A client certificate signed by `issuer`, and its PKCS #8 key.
fn leaf(
    issuer: &Ca,
    alg: &'static SignatureAlgorithm,
    eku: Vec<ExtendedKeyUsagePurpose>,
    edit: impl FnOnce(&mut CertificateParams),
) -> (Vec<u8>, Vec<u8>) {
    let key = KeyPair::generate_for(alg).unwrap();
    let mut params = CertificateParams::new(Vec::<String>::new()).unwrap();
    params.distinguished_name.push(DnType::CommonName, "client");
    params.extended_key_usages = eku;
    params.key_usages = vec![KeyUsagePurpose::DigitalSignature];
    edit(&mut params);
    // rcgen signs with the issuer certificate's subject name and key.
    let issuer_cert = issuer.params.clone().self_signed(&issuer.key).unwrap();
    let cert = params.signed_by(&key, &issuer_cert, &issuer.key).unwrap();
    (cert.der().to_vec(), key.serialize_der())
}

fn client_leaf(issuer: &Ca, alg: &'static SignatureAlgorithm) -> (Vec<u8>, Vec<u8>) {
    leaf(issuer, alg, vec![ExtendedKeyUsagePurpose::ClientAuth], |_| {})
}

fn server_config(roots: &[&Ca], required: bool) -> Arc<Config> {
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    let mut cfg = Config::new(SUITES.to_vec(), GROUPS.to_vec(), key.schemes().to_vec(), Vec::new(), &vec![LEAF.to_vec()]).unwrap();
    assert!(cfg.set_client_auth(CLIENT_SIGS.to_vec(), roots.iter().map(|c| c.der.clone()).collect(), required));
    Arc::new(cfg)
}

fn server(cfg: &Arc<Config>) -> ServerStream<AwsLc> {
    let keys = Arc::new(TicketKeys::new(3600));
    ServerStream::new(cfg.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())).with_tickets(keys))
}

fn builder() -> rustls::ConfigBuilder<ClientConfig, rustls::client::WantsClientCert> {
    let mut roots = RootCertStore::empty();
    roots.add(CertificateDer::from(CA.to_vec())).unwrap();
    ClientConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
}

fn client_config(chain: &[Vec<u8>], key: &[u8]) -> Arc<ClientConfig> {
    let chain = chain.iter().map(|c| CertificateDer::from(c.clone())).collect();
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.to_vec()));
    Arc::new(builder().with_client_auth_cert(chain, key).unwrap())
}

/// Moves bytes both ways until neither side has anything to say, or one
/// side fails: the server's error, or the client's.
fn pump(c: &mut ClientConnection, s: &mut ServerStream<AwsLc>) -> Result<(), String> {
    for _ in 0..20 {
        let mut buf = Vec::new();
        while c.wants_write() {
            c.write_tls(&mut buf).unwrap();
        }
        let mut moved = !buf.is_empty();
        s.read_tls(&buf);
        let r = s.process().map_err(|e| format!("server: {e:?}"));
        let out = s.take_pending();
        if !out.is_empty() {
            moved = true;
            let mut rd = &out[..];
            while !rd.is_empty() {
                c.read_tls(&mut rd).unwrap();
                if let Err(e) = c.process_new_packets() {
                    // The server's own error, if it failed, says more.
                    r?;
                    return Err(format!("client: {e}"));
                }
                let _ = c.reader().read_to_end(&mut Vec::new());
            }
        }
        r?;
        if !moved {
            return Ok(());
        }
    }
    Ok(())
}

fn connect(cc: &Arc<ClientConfig>, sc: &Arc<Config>) -> (ClientConnection, ServerStream<AwsLc>, Result<(), String>) {
    let mut c = ClientConnection::new(cc.clone(), ServerName::try_from("localhost").unwrap()).unwrap();
    let mut s = server(sc);
    let r = pump(&mut c, &mut s);
    (c, s, r)
}

fn connected(cc: &Arc<ClientConfig>, sc: &Arc<Config>) -> (ClientConnection, ServerStream<AwsLc>) {
    let (mut c, mut s, r) = connect(cc, sc);
    r.unwrap();
    assert!(!c.is_handshaking() && !s.is_handshaking());
    // Data both ways.
    c.writer().write_all(b"ping").unwrap();
    pump(&mut c, &mut s).unwrap();
    assert_eq!(s.plaintext(), b"ping");
    s.write(b"pong").unwrap();
    pump(&mut c, &mut s).unwrap();
    let mut got = Vec::new();
    let _ = c.reader().read_to_end(&mut got);
    (c, s)
}

const BAD_CERTIFICATE: u8 = 42;
const UNKNOWN_CA: u8 = 48;
const DECRYPT_ERROR: u8 = 51;
const CERTIFICATE_REQUIRED: u8 = 116;

/// The handshake fails on the server (it is the side that checks), with
/// the alert `alert`.
fn refused(cc: &Arc<ClientConfig>, sc: &Arc<Config>, alert: u8) {
    let (_, s, r) = connect(cc, sc);
    let e = r.expect_err("the server refuses the client");
    assert_eq!(e, format!("server: {:?}", Error::Sent(alert)));
    assert!(s.conn().peer_certificates().is_empty());
}

#[test]
fn every_key_type() {
    for alg in [&PKCS_ECDSA_P256_SHA256, &PKCS_ECDSA_P384_SHA384, &PKCS_ED25519] {
        let root = ca("root", alg);
        let (der, key) = client_leaf(&root, alg);
        let (_, s) = connected(&client_config(&[der.clone()], &key), &server_config(&[&root], true));
        assert_eq!(s.conn().peer_certificates(), &[der][..]);
    }
}

#[test]
fn rsa_client() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let (der, key) = client_leaf(&root, &rcgen::PKCS_RSA_SHA256);
    let (_, s) = connected(&client_config(&[der.clone()], &key), &server_config(&[&root], true));
    assert_eq!(s.conn().peer_certificates(), &[der][..]);
}

#[test]
fn rsa_ca() {
    let root = ca("root", &rcgen::PKCS_RSA_SHA256);
    let (der, key) = client_leaf(&root, &PKCS_ECDSA_P256_SHA256);
    let (_, s) = connected(&client_config(&[der.clone()], &key), &server_config(&[&root], true));
    assert_eq!(s.conn().peer_certificates(), &[der][..]);
}

#[test]
fn intermediate_ca() {
    let root = ca("root", &PKCS_ECDSA_P384_SHA384);
    let mid = intermediate("mid", &root, &PKCS_ECDSA_P256_SHA256);
    let (der, key) = client_leaf(&mid, &PKCS_ECDSA_P256_SHA256);
    let chain = vec![der.clone(), mid.der.clone()];
    let (_, s) = connected(&client_config(&chain, &key), &server_config(&[&root], true));
    assert_eq!(s.conn().peer_certificates(), &chain[..]);
    // The intermediate as the trust anchor works too.
    let (_, s) = connected(&client_config(&[der.clone()], &key), &server_config(&[&mid], true));
    assert_eq!(s.conn().peer_certificates(), &[der][..]);
    // Without the intermediate, the leaf does not chain to the root.
    refused(&client_config(&[chain[0].clone()], &key), &server_config(&[&root], true), UNKNOWN_CA);
}

#[test]
fn one_of_several_roots() {
    let a = ca("a", &PKCS_ECDSA_P256_SHA256);
    let b = ca("b", &PKCS_ECDSA_P256_SHA256);
    let (der, key) = client_leaf(&b, &PKCS_ECDSA_P256_SHA256);
    connected(&client_config(&[der], &key), &server_config(&[&a, &b], true));
}

#[test]
fn no_certificate() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let anon = Arc::new(builder().with_no_client_auth());
    // Optional: connects, with no client identity.
    let (_, s) = connected(&anon, &server_config(&[&root], false));
    assert!(s.conn().peer_certificates().is_empty());
    // Required: certificate_required.
    refused(&anon, &server_config(&[&root], true), CERTIFICATE_REQUIRED);
}

#[test]
fn untrusted_issuer() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let other = ca("root", &PKCS_ECDSA_P256_SHA256); // same name, other key
    let (der, key) = client_leaf(&other, &PKCS_ECDSA_P256_SHA256);
    refused(&client_config(&[der], &key), &server_config(&[&root], true), UNKNOWN_CA);
    // A CA certificate (keyCertSign only) is not a client's.
    refused(&client_config(&[other.der.clone()], &other.key.serialize_der()), &server_config(&[&root], false), BAD_CERTIFICATE);
}

#[test]
fn expired_and_not_yet_valid() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let (old, key) = leaf(&root, &PKCS_ECDSA_P256_SHA256, vec![ExtendedKeyUsagePurpose::ClientAuth], |p| {
        p.not_before = rcgen::date_time_ymd(2001, 1, 1);
        p.not_after = rcgen::date_time_ymd(2002, 1, 1);
    });
    refused(&client_config(&[old], &key), &server_config(&[&root], true), BAD_CERTIFICATE);
    let (new, key) = leaf(&root, &PKCS_ECDSA_P256_SHA256, vec![ExtendedKeyUsagePurpose::ClientAuth], |p| {
        p.not_before = rcgen::date_time_ymd(2090, 1, 1);
        p.not_after = rcgen::date_time_ymd(2091, 1, 1);
    });
    refused(&client_config(&[new], &key), &server_config(&[&root], true), BAD_CERTIFICATE);
}

#[test]
fn key_purpose() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    // A server-only certificate is not a client's.
    let (der, key) = leaf(&root, &PKCS_ECDSA_P256_SHA256, vec![ExtendedKeyUsagePurpose::ServerAuth], |_| {});
    refused(&client_config(&[der], &key), &server_config(&[&root], true), BAD_CERTIFICATE);
    // Any purpose, or no extendedKeyUsage at all, is fine.
    let (der, key) = leaf(&root, &PKCS_ECDSA_P256_SHA256, vec![ExtendedKeyUsagePurpose::Any], |_| {});
    connected(&client_config(&[der], &key), &server_config(&[&root], true));
    let (der, key) = leaf(&root, &PKCS_ECDSA_P256_SHA256, vec![], |_| {});
    connected(&client_config(&[der], &key), &server_config(&[&root], true));
}

/// Sends a certificate but signs with another key.
#[derive(Debug)]
struct WrongKey(Arc<CertifiedKey>);

impl ResolvesClientCert for WrongKey {
    fn resolve(&self, _: &[&[u8]], _: &[SignatureScheme]) -> Option<Arc<CertifiedKey>> {
        Some(self.0.clone())
    }
    fn has_certs(&self) -> bool {
        true
    }
}

#[test]
fn wrong_certificate_verify() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let (der, _) = client_leaf(&root, &PKCS_ECDSA_P256_SHA256);
    let other = KeyPair::generate_for(&PKCS_ECDSA_P256_SHA256).unwrap();
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(other.serialize_der()));
    let signer = rustls::crypto::aws_lc_rs::sign::any_supported_type(&key).unwrap();
    let ck = Arc::new(CertifiedKey::new(vec![CertificateDer::from(der)], signer));
    let cc = Arc::new(builder().with_client_cert_resolver(Arc::new(WrongKey(ck))));
    refused(&cc, &server_config(&[&root], true), DECRYPT_ERROR);
    refused(&cc, &server_config(&[&root], false), DECRYPT_ERROR);
}

#[test]
fn no_resumption_or_tickets() {
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let (der, key) = client_leaf(&root, &PKCS_ECDSA_P256_SHA256);
    let chain = [CertificateDer::from(der)];
    let mut cc = builder().with_client_auth_cert(chain.to_vec(), PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key))).unwrap();
    cc.resumption = Resumption::store(Arc::new(ClientSessionMemoryCache::new(8)));
    cc.enable_early_data = true;
    let cc = Arc::new(cc);
    let sc = server_config(&[&root], true);
    for _ in 0..2 {
        let (c, s) = connected(&cc, &sc);
        assert_eq!(c.handshake_kind(), Some(HandshakeKind::Full));
        assert!(!s.conn().early_accepted());
    }
}

/// Accepts any server certificate (the tests here are about the client's).
#[derive(Debug)]
struct AnyServer;

impl ServerCertVerifier for AnyServer {
    fn verify_server_cert(&self, _: &CertificateDer, _: &[CertificateDer], _: &ServerName, _: &[u8], _: UnixTime) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }
    fn verify_tls12_signature(&self, _: &[u8], _: &CertificateDer, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }
    fn verify_tls13_signature(&self, _: &[u8], _: &CertificateDer, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        rustls::crypto::aws_lc_rs::default_provider().signature_verification_algorithms.supported_schemes()
    }
}

#[test]
fn long_chain_over_several_records() {
    // A chain longer than one record (16 KB): the client's Certificate
    // spans records, and its CertificateVerify and Finished follow.
    let root = ca("root", &PKCS_ECDSA_P256_SHA256);
    let (der, key) = leaf(&root, &PKCS_ECDSA_P256_SHA256, vec![ExtendedKeyUsagePurpose::ClientAuth], |p| {
        for i in 0..800 {
            p.subject_alt_names.push(rcgen::SanType::DnsName(format!("host-{i:04}.a-rather-long-name.example.com").try_into().unwrap()));
        }
    });
    assert!(der.len() > 16384);
    let chain = vec![CertificateDer::from(der.clone())];
    let mut cc = ClientConfig::builder_with_provider(Arc::new(rustls::crypto::aws_lc_rs::default_provider()))
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .dangerous()
        .with_custom_certificate_verifier(Arc::new(AnyServer))
        .with_client_auth_cert(chain, PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key)))
        .unwrap();
    cc.resumption = Resumption::disabled();
    let (_, s) = connected(&Arc::new(cc), &server_config(&[&root], true));
    assert_eq!(s.conn().peer_certificates(), &[der][..]);
}
