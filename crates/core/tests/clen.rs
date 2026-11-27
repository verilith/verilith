//! `BodyLen`: a body counted against its declared Content-Length.
use verilith_core::clen::BodyLen;

#[test]
fn body_len() {
    let mut b = BodyLen::new();
    assert!(b.complete());
    assert!(b.add(3));
    assert!(!b.declare(2), "less than already arrived");
    assert!(b.declare(5));
    assert!(b.declare(5), "the same length again");
    assert!(!b.declare(6), "a different length");
    assert!(!b.complete());
    assert!(!b.add(3), "past the length");
    assert_eq!(b.received(), 3);
    assert!(b.add(2));
    assert!(b.complete());
    assert!(!b.add(1));
    let mut c = BodyLen::new();
    assert!(c.add(u64::MAX));
    assert!(!c.add(1), "past u64::MAX");
}
