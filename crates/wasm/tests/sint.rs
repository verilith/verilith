//! Checks the signed-integer and bit-count primitives (`src/sint.rs`; only
//! the popcounts are still trusted) against an independent `i128` evaluation of their specs
//! (the definitions in `src/num.rs`: Verus `/` and `%` on `int` are
//! Euclidean).
use verilith_wasm::sint::*;

fn m32(i: i128) -> u32 { i.rem_euclid(1 << 32) as u32 }
fn m64(i: i128) -> u64 { i.rem_euclid(1 << 64) as u64 }
fn s32(a: u32) -> i128 { if a < 0x8000_0000 { a as i128 } else { a as i128 - (1 << 32) } }
fn s64(a: u64) -> i128 { if a < 0x8000_0000_0000_0000 { a as i128 } else { a as i128 - (1 << 64) } }
fn tdiv(x: i128, y: i128) -> i128 {
    let q = x.abs().div_euclid(y.abs());
    if (x < 0) != (y < 0) { -q } else { q }
}
fn trem(x: i128, y: i128) -> i128 { x - y * tdiv(x, y) }
fn pow2(k: u32) -> i128 { 1i128 << k }
fn sext(a: u128, n: u32) -> i128 {
    let x = (a % (1u128 << n)) as i128;
    if x < pow2(n - 1) { x } else { x - pow2(n) }
}
fn clz(a: u128, n: u32) -> u32 {
    if n == 0 { 0 } else if a as i128 >= pow2(n - 1) { 0 } else { 1 + clz(a, n - 1) }
}
fn ctz(a: u128, n: u32) -> u32 {
    if n == 0 { 0 } else if a % 2 == 1 { 0 } else { 1 + ctz(a / 2, n - 1) }
}
fn popcnt(a: u128) -> u32 { if a == 0 { 0 } else { (a % 2) as u32 + popcnt(a / 2) } }

fn values32() -> Vec<u32> {
    let mut v = vec![0, 1, 2, 3, 7, 8, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fff_ffff, 0x8000_0000,
        0x8000_0001, 0xffff_fffe, 0xffff_ffff];
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    for _ in 0..300 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        v.push(x as u32);
    }
    v
}

fn values64() -> Vec<u64> {
    let mut v: Vec<u64> = vec![0, 1, 2, 0x7f, 0x80, 0xffff, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff,
        0x1_0000_0000, 0x7fff_ffff_ffff_ffff, 0x8000_0000_0000_0000, 0x8000_0000_0000_0001, u64::MAX - 1, u64::MAX];
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    for _ in 0..300 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        v.push(x);
    }
    v
}

#[test]
fn signed32() {
    let vs = values32();
    for &a in &vs {
        for &b in &vs {
            assert_eq!(lt_s32(a, b), s32(a) < s32(b));
            if b != 0 && !(a == 0x8000_0000 && b == 0xffff_ffff) {
                assert_eq!(div_s32(a, b), m32(tdiv(s32(a), s32(b))), "{a:x} / {b:x}");
                assert_eq!(rem_s32(a, b), m32(trem(s32(a), s32(b))), "{a:x} % {b:x}");
            }
        }
        for k in 0..32 {
            assert_eq!(shr_s32(a, k), m32(s32(a).div_euclid(pow2(k))));
        }
        for n in [8, 16] {
            assert_eq!(sext32(a, n), m32(sext(a as u128, n)));
        }
        assert_eq!(clz32(a), clz(a as u128, 32));
        assert_eq!(ctz32(a), ctz(a as u128, 32));
        assert_eq!(popcnt32(a), popcnt(a as u128));
    }
}

#[test]
fn signed64() {
    let vs = values64();
    for &a in &vs {
        for &b in &vs {
            assert_eq!(lt_s64(a, b), s64(a) < s64(b));
            if b != 0 && !(a == 0x8000_0000_0000_0000 && b == u64::MAX) {
                assert_eq!(div_s64(a, b), m64(tdiv(s64(a), s64(b))), "{a:x} / {b:x}");
                assert_eq!(rem_s64(a, b), m64(trem(s64(a), s64(b))), "{a:x} % {b:x}");
            }
        }
        for k in 0..64 {
            assert_eq!(shr_s64(a, k), m64(s64(a).div_euclid(pow2(k as u32))));
        }
        for n in [8, 16, 32] {
            assert_eq!(sext64(a, n), m64(sext(a as u128, n)));
        }
        assert_eq!(clz64(a), clz(a as u128, 64) as u64);
        assert_eq!(ctz64(a), ctz(a as u128, 64) as u64);
        assert_eq!(popcnt64(a), popcnt(a as u128) as u64);
    }
}
