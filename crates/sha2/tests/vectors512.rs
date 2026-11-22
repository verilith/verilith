//! The SHA-512 family's constants from their definitions, the SHA-512/t IV
//! generation function (FIPS 180-4 §5.3.6), and the examples of FIPS
//! 180-2 Appendix C and D and of NIST's SHA-512/t examples.
use verilith_sha2::hash512::Engine512;
use verilith_sha2::spec512::{IV384, IV512, IV512_224, IV512_256, K};
use verilith_sha2::*;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn primes(n: usize) -> Vec<u64> {
    let mut p = Vec::new();
    let mut k = 2u64;
    while p.len() < n {
        if p.iter().all(|q| k % q != 0) {
            p.push(k);
        }
        k += 1;
    }
    p
}

/// Non-negative integers as little-endian u64 limbs.
fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = r[i + j] as u128 + x as u128 * y as u128 + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
        r[i + b.len()] = carry as u64;
    }
    r
}

fn le(a: &[u64], b: &[u64]) -> bool {
    let n = a.len().max(b.len());
    for i in (0..n).rev() {
        let (x, y) = (*a.get(i).unwrap_or(&0), *b.get(i).unwrap_or(&0));
        if x != y {
            return x < y;
        }
    }
    true
}

/// floor((p * 2^(64 * shift))^(1/r)), exactly, as a u128.
fn root(p: u64, shift: usize, r: u32) -> u128 {
    let mut v = vec![0u64; shift];
    v.push(p);
    let (mut lo, mut hi) = (0u128, 1u128 << 72);
    while hi - lo > 1 {
        let m = (lo + hi) / 2;
        let ml = [m as u64, (m >> 64) as u64];
        let mut pow = ml.to_vec();
        for _ in 1..r {
            pow = mul(&pow, &ml);
        }
        if le(&pow, &v) {
            lo = m;
        } else {
            hi = m;
        }
    }
    lo
}

#[test]
fn constants_are_their_definitions() {
    // K: the first 64 bits of the fractional parts of the cube roots of the
    // first 80 primes (§4.2.3): floor(cbrt(p * 2^192)) mod 2^64.
    let p = primes(80);
    for t in 0..80 {
        assert_eq!(K[t], root(p[t], 3, 3) as u64, "K[{t}]");
    }
    // SHA-256's constants are the first 32 bits of the same roots.
    for t in 0..64 {
        assert_eq!(verilith_sha2::spec::K[t], (K[t] >> 32) as u32);
    }
    // H(0) for SHA-512 and SHA-384: square roots of the first 8 primes and
    // of the 9th to 16th (§5.3.5, §5.3.4).
    for i in 0..8 {
        assert_eq!(IV512[i], root(p[i], 2, 2) as u64, "IV512[{i}]");
        assert_eq!(IV384[i], root(p[8 + i], 2, 2) as u64, "IV384[{i}]");
    }
}

#[test]
fn sha512_t_iv_generation() {
    // §5.3.6: SHA-512 with H(0) XOR a5a5...a5, of the string "SHA-512/t".
    let mut iv = IV512;
    for w in iv.iter_mut() {
        *w ^= 0xa5a5_a5a5_a5a5_a5a5;
    }
    for (t, want) in [("224", IV512_224), ("256", IV512_256)] {
        let mut e = Engine512::new(iv);
        e.update(format!("SHA-512/{t}").as_bytes());
        assert_eq!(e.finish(), want, "SHA-512/{t}");
    }
}

const M896: &[u8] = b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu";

#[test]
fn examples() {
    let a = vec![b'a'; 1_000_000];
    assert_eq!(hex(&sha512(b"abc")), "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f");
    assert_eq!(hex(&sha512(b"")), "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e");
    assert_eq!(hex(&sha512(M896)), "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909");
    assert_eq!(hex(&sha512(&a)), "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973ebde0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b");
    assert_eq!(hex(&sha384(b"abc")), "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7");
    assert_eq!(hex(&sha384(b"")), "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b");
    assert_eq!(hex(&sha384(M896)), "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039");
    assert_eq!(hex(&sha384(&a)), "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b07b8b3dc38ecc4ebae97ddd87f3d8985");
    assert_eq!(hex(&sha512_224(b"abc")), "4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa");
    assert_eq!(hex(&sha512_256(b"abc")), "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23");
    assert_eq!(hex(&sha512_224(b"")), "6ed0dd02806fa89e25de060c19d3ac86cabb87d6a0ddd05c333b84f4");
    assert_eq!(hex(&sha512_256(b"")), "c672b8d1ef56ed28ab87c3622c5114069bdd3ad7b8f9737498d0c01ecef0967a");
    // The million a's in pieces that are not a multiple of the block.
    let mut h = Sha512::new();
    for c in a.chunks(999) {
        h.update(c);
    }
    assert_eq!(h.finalize(), sha512(&a));
}
