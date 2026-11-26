//! QUIC's keys (RFC 9001 §5) against the values of RFC 9001 Appendix A.
use verilith_tls::keys::*;
use verilith_tls::spec_keys::HashAlg;

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

#[test]
fn initial_keys_appendix_a1() {
    let dcid = hex("8394c8f03e515708");
    let (c, s) = initial_secrets_x(&dcid);
    assert_eq!(c.as_slice(), hex("c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea"));
    let (k, iv, hp) = quic_keys_x(HashAlg::Sha256, &c, 16);
    assert_eq!(k.as_slice(), hex("1f369613dd76d5467730efcbe3b1a22d"));
    assert_eq!(iv.as_slice(), hex("fa044b2f42a3fd3b46fb255c"));
    assert_eq!(hp.as_slice(), hex("9f50449e04a0e810283a1e9933adedd2"));
    let (k, iv, hp) = quic_keys_x(HashAlg::Sha256, &s, 16);
    assert_eq!(k.as_slice(), hex("cf3a5331653c364c88f0f379b6067e37"));
    assert_eq!(iv.as_slice(), hex("0ac1493ca1905853b0bba03e"));
    assert_eq!(hp.as_slice(), hex("c206b8d9b9f0f37644430b490eeaa314"));
}

#[test]
fn key_update_appendix_a5() {
    // A.5: ChaCha20-Poly1305 short header packet; the secret and its
    // key update.
    let secret = hex("9ac312a7f877468ebe69422748ad00a15443f18203a07d6060f688f30f21632b");
    let sec = Secret::from_slice(&secret, 32);
    let (k, iv, hp) = quic_keys_x(HashAlg::Sha256, &sec, 32);
    assert_eq!(k.as_slice(), hex("c6d98ff3441c3fe1b2182094f69caa2ed4b716b65488960a7a984979fb23e1c8"));
    assert_eq!(iv.as_slice(), hex("e0459b3474bdd0e44a41c144"));
    assert_eq!(hp.as_slice(), hex("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4"));
    let ku = quic_next_x(HashAlg::Sha256, &sec);
    assert_eq!(ku.as_slice(), hex("1223504755036d556342ee9361d253421a826c9ecdf3c7148684b36b714881f9"));
}
