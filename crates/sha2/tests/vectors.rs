//! The FIPS 180-4 constants from their definition, and the examples of
//! FIPS 180-2 Appendix B (SHA-256) and FIPS 180-2 Change Notice 1 (SHA-224).
use verilith_sha2::spec::{IV224, IV256, K};
use verilith_sha2::{sha224, sha256, Sha224, Sha256};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn primes(n: usize) -> Vec<u128> {
    let mut p = Vec::new();
    let mut k = 2u128;
    while p.len() < n {
        if p.iter().all(|q| k % q != 0) {
            p.push(k);
        }
        k += 1;
    }
    p
}

/// The largest x with x^r <= v, exactly.
fn iroot(v: u128, r: u32) -> u128 {
    let (mut lo, mut hi) = (0u128, 1u128 << (128 / r + 1));
    while hi - lo > 1 {
        let m = (lo + hi) / 2;
        if m.checked_pow(r).is_some_and(|x| x <= v) {
            lo = m;
        } else {
            hi = m;
        }
    }
    lo
}

/// a * b as (high, low) 128-bit halves.
fn mul_wide(a: u128, b: u128) -> (u128, u128) {
    let m = u64::MAX as u128;
    let (a1, a0, b1, b0) = (a >> 64, a & m, b >> 64, b & m);
    let (lo, mid1, mid2, hi) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
    let (mid, c1) = mid1.overflowing_add(mid2);
    let (low, c2) = lo.overflowing_add(mid << 64);
    (hi + (mid >> 64) + ((c1 as u128) << 64) + c2 as u128, low)
}

/// floor(sqrt(v * 2^128)), exactly, for small v.
fn isqrt_shl128(v: u128) -> u128 {
    let (mut lo, mut hi) = (0u128, 1u128 << 72);
    while hi - lo > 1 {
        let m = (lo + hi) / 2;
        if mul_wide(m, m) <= (v, 0) {
            lo = m;
        } else {
            hi = m;
        }
    }
    lo
}

#[test]
fn constants_are_their_definitions() {
    // K: the first 32 bits of the fractional parts of the cube roots of
    // the first 64 primes (§4.2.2). floor(cbrt(p) * 2^32) = iroot(p * 2^96, 3).
    for (t, p) in primes(64).into_iter().enumerate() {
        assert_eq!(K[t], iroot(p << 96, 3) as u32, "K[{t}]");
    }
    // SHA-256's H(0): the same of the square roots of the first 8 primes
    // (§5.3.3).
    let p = primes(16);
    for i in 0..8 {
        assert_eq!(IV256[i], iroot(p[i] << 64, 2) as u32, "IV256[{i}]");
    }
    // SHA-224's: the second 32 bits of the square roots of the 9th to
    // 16th primes (§5.3.2): floor(sqrt(p) * 2^64) mod 2^32, where
    // p * 2^128 needs more than 128 bits.
    for i in 0..8 {
        assert_eq!(IV224[i], isqrt_shl128(p[8 + i]) as u32, "IV224[{i}]");
    }
}

const M448: &[u8] = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
const M896: &[u8] = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";

#[test]
fn sha256_examples() {
    assert_eq!(hex(&sha256(b"")), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert_eq!(hex(&sha256(b"abc")), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert_eq!(hex(&sha256(M448)), "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
    assert_eq!(hex(&sha256(M896)), "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1");
    let a = vec![b'a'; 1_000_000];
    assert_eq!(hex(&sha256(&a)), "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
    // The million a's again, as 1000 updates of 1000.
    let mut h = Sha256::new();
    for _ in 0..1000 {
        h.update(&a[..1000]);
    }
    assert_eq!(hex(&h.finalize()), "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

#[test]
fn sha224_examples() {
    assert_eq!(hex(&sha224(b"")), "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f");
    assert_eq!(hex(&sha224(b"abc")), "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7");
    assert_eq!(hex(&sha224(M448)), "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525");
    let a = vec![b'a'; 1_000_000];
    assert_eq!(hex(&sha224(&a)), "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67");
    let mut h = Sha224::new();
    for c in a.chunks(999) {
        h.update(c);
    }
    assert_eq!(hex(&h.finalize()), "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67");
}

#[test]
fn finalize_leaves_the_hasher_as_it_was() {
    let mut h = Sha256::new();
    h.update(b"ab");
    let _ = h.finalize();
    h.update(b"c");
    assert_eq!(h.finalize(), sha256(b"abc"));
}
