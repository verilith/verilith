//! verilith-tls's QUIC handshake (RFC 9001) with rustls's QUIC client, in
//! memory: every suite, HelloRetryRequest, resumption, the transport
//! parameters both ways, and packet protection keys derived from the
//! exposed secrets checked against the client's.
use aws_lc_rs::aead::quic::{HeaderProtectionKey, AES_128, AES_256, CHACHA20};
use aws_lc_rs::aead::{Aad, LessSafeKey, Nonce, UnboundKey};
use rustls::pki_types::{CertificateDer, ServerName};
use rustls::quic::{self, KeyChange, Keys};
use rustls::{ClientConfig, RootCertStore};
use std::sync::Arc;
use verilith_tls::keys::{quic_keys_x, Secret};
use verilith_tls::quic::{Event, Out, QuicServer, HANDSHAKE, INITIAL};
use verilith_tls::server::Config;
use verilith_tls::spec_keys::HashAlg;
use verilith_tls_aws_lc::*;

const LEAF: &[u8] = include_bytes!("data/leaf.der");
const CA: &[u8] = include_bytes!("data/ca.der");
const KEY: &[u8] = include_bytes!("data/leaf.key.der");

const SERVER_TP: &[u8] = b"\x04\x04\x80\x10\x00\x00\x0f\x00";
const CLIENT_TP: &[u8] = b"\x01\x02\x67\x10\x0f\x04\x01\x02\x03\x04";

fn server_config(suites: &[u16], groups: &[u16], tickets: u8) -> Arc<Config> {
    let key = SigningKey::from_pkcs8(KEY).unwrap();
    let mut c = Config::new(suites.to_vec(), groups.to_vec(), key.schemes().to_vec(), b"\x02h3".to_vec(), &vec![LEAF.to_vec()]).unwrap();
    c.set_tickets(tickets, 3600);
    Arc::new(c)
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

fn hash_of(suite: u16) -> HashAlg {
    if suite == TLS_AES_256_GCM_SHA384 { HashAlg::Sha384 } else { HashAlg::Sha256 }
}

/// A packet sealed by `keys` (rustls) opens under the keys derived from
/// `secret` (verilith-tls), and their header protection masks agree; and
/// the other way round.
fn same_keys(suite: u16, secret: &Secret, theirs: &dyn quic::PacketKey, their_hp: &dyn quic::HeaderProtectionKey, theirs_seal: bool) {
    let kl = if suite == TLS_AES_128_GCM_SHA256 { 16 } else { 32 };
    let (k, iv, hp) = quic_keys_x(hash_of(suite), secret, kl);
    let alg = match suite {
        TLS_AES_128_GCM_SHA256 => &aws_lc_rs::aead::AES_128_GCM,
        TLS_AES_256_GCM_SHA384 => &aws_lc_rs::aead::AES_256_GCM,
        _ => &aws_lc_rs::aead::CHACHA20_POLY1305,
    };
    let ours = LessSafeKey::new(UnboundKey::new(alg, k.as_slice()).unwrap());
    let header = [0x43u8, 1, 2, 3, 4, 5, 6, 7, 8, 0x12, 0x34];
    let payload: Vec<u8> = (0..100u8).collect();
    for pn in [0u64, 1, 0x1234, 0xffff_ffff_ffff] {
        let mut nonce = [0u8; 12];
        nonce.copy_from_slice(iv.as_slice());
        for (i, b) in pn.to_be_bytes().iter().enumerate() {
            nonce[4 + i] ^= b;
        }
        let mut p = payload.clone();
        if theirs_seal {
            let tag = theirs.encrypt_in_place(pn, &header, &mut p).unwrap();
            p.extend_from_slice(tag.as_ref());
            let pt = ours.open_in_place(Nonce::assume_unique_for_key(nonce), Aad::from(&header[..]), &mut p).unwrap();
            assert_eq!(pt, &payload[..]);
        } else {
            ours.seal_in_place_append_tag(Nonce::assume_unique_for_key(nonce), Aad::from(&header[..]), &mut p).unwrap();
            let pt = theirs.decrypt_in_place(pn, &header, &mut p).unwrap();
            assert_eq!(pt, &payload[..]);
        }
    }
    let hpalg = match suite {
        TLS_AES_128_GCM_SHA256 => &AES_128,
        TLS_AES_256_GCM_SHA384 => &AES_256,
        _ => &CHACHA20,
    };
    let hk = HeaderProtectionKey::new(hpalg, hp.as_slice()).unwrap();
    let sample: [u8; 16] = core::array::from_fn(|i| (i * 13 + 5) as u8);
    let mask = hk.new_mask(&sample).unwrap();
    let mut first = 0u8;
    let mut pnb = [0u8; 4];
    if theirs_seal {
        their_hp.encrypt_in_place(&sample, &mut first, &mut pnb).unwrap();
    } else {
        their_hp.decrypt_in_place(&sample, &mut first, &mut pnb).unwrap();
    }
    // A short header's first byte (0) is masked in its low 5 bits; the
    // packet number length (first & 3, after unmasking) is that many bytes
    // plus one.
    assert_eq!(first, mask[0] & 0x1f);
    // Sealing masks as many packet number bytes as the unmasked first byte
    // says (1), opening as many as the unmasked one says.
    let n = if theirs_seal { 1 } else { (first & 3) as usize + 1 };
    for i in 0..n {
        assert_eq!(pnb[i], mask[1 + i]);
    }
}

struct Run {
    resumed: bool,
}

/// One QUIC handshake between a rustls client and a verilith-tls server.
fn handshake(cc: &Arc<ClientConfig>, sc: &Arc<Config>, prov: AwsLc) -> Run {
    let mut c = quic::ClientConnection::new(cc.clone(), quic::Version::V1, ServerName::try_from("localhost").unwrap(), CLIENT_TP.to_vec()).unwrap();
    let mut s = QuicServer::new(sc.clone(), prov, SERVER_TP.to_vec()).unwrap();
    let mut level = INITIAL;
    let mut hs_keys: Option<Keys> = None;
    let mut done = false;
    let mut ap_checked = false;
    for _ in 0..10 {
        let mut buf = Vec::new();
        let change = c.write_hs(&mut buf);
        if !buf.is_empty() {
            let mut out = Out::new();
            let ev = s.read(level, &buf, &mut out).expect("server accepts");
            if ev == Event::Accepted {
                let (_, ss) = s.hs_secrets().unwrap();
                let _ = ss;
            }
            if ev == Event::Done {
                done = true;
            }
            if !out.initial.is_empty() {
                c.read_hs(&out.initial).unwrap();
            }
            if !out.handshake.is_empty() {
                // The client needs its Handshake keys before reading the
                // flight: write_hs hands them over after ServerHello.
                let mut b2 = Vec::new();
                let ch2 = c.write_hs(&mut b2);
                assert!(b2.is_empty());
                if let Some(KeyChange::Handshake { keys }) = ch2 {
                    let suite = s.suite().unwrap();
                    let (cs, ss) = s.hs_secrets().unwrap();
                    same_keys(suite, cs, &*keys.local.packet, &*keys.local.header, true);
                    same_keys(suite, ss, &*keys.remote.packet, &*keys.remote.header, false);
                    hs_keys = Some(keys);
                }
                c.read_hs(&out.handshake).unwrap();
                level = HANDSHAKE;
            }
            if !out.one_rtt.is_empty() {
                c.read_hs(&out.one_rtt).unwrap();
            }
        }
        if let Some(KeyChange::OneRtt { keys, .. }) = change {
            let suite = s.suite().unwrap();
            let (ca, sa) = s.ap_secrets().unwrap();
            same_keys(suite, ca, &*keys.local.packet, &*keys.local.header, true);
            same_keys(suite, sa, &*keys.remote.packet, &*keys.remote.header, false);
            ap_checked = true;
        }
        if done && !c.is_handshaking() {
            break;
        }
    }
    assert!(done && s.is_connected() && !c.is_handshaking());
    assert!(hs_keys.is_some() && ap_checked);
    assert_eq!(c.quic_transport_parameters(), Some(SERVER_TP));
    assert_eq!(s.peer_params(), CLIENT_TP);
    assert_eq!(s.alpn(), Some(&b"h3"[..]));
    assert_eq!(c.alpn_protocol(), Some(&b"h3"[..]));
    Run { resumed: c.handshake_kind() == Some(rustls::HandshakeKind::Resumed) }
}

#[test]
fn every_suite_and_group() {
    use rustls::crypto::aws_lc_rs::kx_group;
    let groups: [(&'static dyn rustls::crypto::SupportedKxGroup, u16); 3] =
        [(kx_group::X25519, X25519), (kx_group::SECP256R1, SECP256R1), (kx_group::X25519MLKEM768, X25519MLKEM768)];
    for suite in SUITES {
        for (g, id) in groups {
            let sc = server_config(&[suite], &[id], 0);
            let r = handshake(&client_config(Some(vec![g]), &[b"h3"]), &sc, AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())));
            assert!(!r.resumed);
        }
    }
}

#[test]
fn hello_retry_request() {
    use rustls::crypto::aws_lc_rs::kx_group;
    let sc = server_config(&SUITES, &[SECP256R1], 0);
    let cc = client_config(Some(vec![kx_group::X25519, kx_group::SECP256R1]), &[b"h3"]);
    handshake(&cc, &sc, AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())));
}

#[test]
fn resumption() {
    let sc = server_config(&SUITES, &GROUPS, 2);
    let cc = client_config(None, &[b"h3"]);
    let key = Arc::new(SigningKey::from_pkcs8(KEY).unwrap());
    let tickets = Arc::new(TicketKeys::new(3600));
    let first = handshake(&cc, &sc, AwsLc::shared(key.clone()).with_tickets(tickets.clone()));
    assert!(!first.resumed);
    let second = handshake(&cc, &sc, AwsLc::shared(key.clone()).with_tickets(tickets.clone()));
    assert!(second.resumed, "the second handshake resumes from a ticket");
}

#[test]
fn alpn_is_required() {
    let sc = server_config(&SUITES, &GROUPS, 0);
    for alpn in [&[][..], &[&b"h2"[..]][..]] {
        let cc = client_config(None, alpn);
        let mut c = quic::ClientConnection::new(cc, quic::Version::V1, ServerName::try_from("localhost").unwrap(), CLIENT_TP.to_vec()).unwrap();
        let mut s = QuicServer::new(sc.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())), SERVER_TP.to_vec()).unwrap();
        let mut buf = Vec::new();
        c.write_hs(&mut buf);
        let mut out = Out::new();
        // no_application_protocol (120), as CRYPTO_ERROR.
        assert_eq!(s.read(INITIAL, &buf, &mut out), Err(0x100 + 120));
    }
}

#[test]
fn split_and_wrong_level() {
    let sc = server_config(&SUITES, &GROUPS, 0);
    let cc = client_config(None, &[b"h3"]);
    let mut c = quic::ClientConnection::new(cc.clone(), quic::Version::V1, ServerName::try_from("localhost").unwrap(), CLIENT_TP.to_vec()).unwrap();
    let mut s = QuicServer::new(sc.clone(), AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())), SERVER_TP.to_vec()).unwrap();
    let mut buf = Vec::new();
    c.write_hs(&mut buf);
    // A byte at a time: nothing until the last byte.
    let mut out = Out::new();
    for (i, b) in buf.iter().enumerate() {
        let ev = s.read(INITIAL, std::slice::from_ref(b), &mut out).unwrap();
        assert_eq!(ev == Event::Accepted, i == buf.len() - 1);
    }
    assert!(!out.initial.is_empty() && !out.handshake.is_empty());
    // The ClientHello at the Handshake level is unexpected_message.
    let mut c = quic::ClientConnection::new(cc, quic::Version::V1, ServerName::try_from("localhost").unwrap(), CLIENT_TP.to_vec()).unwrap();
    let mut s = QuicServer::new(sc, AwsLc::new(Some(SigningKey::from_pkcs8(KEY).unwrap())), SERVER_TP.to_vec()).unwrap();
    let mut buf = Vec::new();
    c.write_hs(&mut buf);
    assert_eq!(s.read(HANDSHAKE, &buf, &mut Out::new()), Err(0x100 + 10));
}
