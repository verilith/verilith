//! `antireplay::Register` (whose properties are proven) on a few timelines.
use verilith_tls::antireplay::{Register, SPAN_MS, WINDOW_MS};

const T0: u64 = 1_800_000_000_000; // ms since the epoch
const ISSUED: u64 = T0 / 1000 - 5; // a ticket issued 5 s before T0
const ADD: u32 = 0x9e37_79b9;

/// The obfuscated age a client sends for a ticket it thinks `age` ms old.
fn obf(age: u32) -> u32 {
    age.wrapping_add(ADD)
}

#[test]
fn fresh_once() {
    let mut r = Register::new(T0);
    assert!(r.claim(1, T0, obf(5000), ISSUED, ADD));
    // The same ClientHello again, at once and later in its window.
    assert!(!r.claim(1, T0, obf(5000), ISSUED, ADD));
    assert!(!r.claim(1, T0 + WINDOW_MS, obf(5000), ISSUED, ADD));
    // Another ClientHello is taken.
    assert!(r.claim(2, T0 + 1, obf(5001), ISSUED, ADD));
}

#[test]
fn stale_or_from_the_future_is_refused() {
    let mut r = Register::new(T0);
    // The client thinks the ticket 5 s old; the server, 5 s + 11 s.
    assert!(!r.claim(1, T0 + 11_000, obf(5000), ISSUED, ADD));
    // A ticket issued after now.
    assert!(!r.claim(2, T0, obf(0), T0 / 1000 + 10, ADD));
    // A clock that went back before the generation began.
    assert!(!r.claim(3, T0 - 1, obf(5000), ISSUED, ADD));
    assert!(r.claim(4, T0 + 10_000, obf(5000), ISSUED, ADD));
}

#[test]
fn remembered_across_one_generation() {
    let mut r = Register::new(T0);
    assert!(r.claim(7, T0 + SPAN_MS - 1, obf(5000 + SPAN_MS as u32 - 1), ISSUED, ADD));
    // The next generation starts; key 7 is in the one before it.
    assert!(!r.claim(7, T0 + SPAN_MS + 5, obf(5000 + SPAN_MS as u32 + 5), ISSUED, ADD));
    // Two generations on, it is forgotten (and its ClientHello long stale).
    assert!(r.claim(7, T0 + 3 * SPAN_MS, obf(5000 + 3 * SPAN_MS as u32), ISSUED, ADD));
}
