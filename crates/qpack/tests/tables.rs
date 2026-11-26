//! The static table (`stable.rs`, trusted data) against entries quoted from
//! RFC 9204 Appendix A, and the encoder's untrusted static-table index
//! against the table itself.
use verilith_qpack::encoder::static_find;
use verilith_qpack::table::static_entry;

#[test]
fn quoted_entries() {
    let quoted: [(usize, &str, &str); 12] = [
        (0, ":authority", ""),
        (1, ":path", "/"),
        (17, ":method", "GET"),
        (25, ":status", "200"),
        (31, "accept-encoding", "gzip, deflate, br"),
        (46, "content-type", "application/json"),
        (63, ":status", "100"),
        (71, ":status", "500"),
        (72, "accept-language", ""),
        (94, "upgrade-insecure-requests", "1"),
        (97, "x-frame-options", "deny"),
        (98, "x-frame-options", "sameorigin"),
    ];
    for (i, n, v) in quoted {
        let (en, ev) = static_entry(i);
        assert_eq!((en, ev), (n.as_bytes(), v.as_bytes()), "entry {i}");
    }
}

#[test]
fn lowercase_and_short() {
    for i in 0..99 {
        let (n, v) = static_entry(i);
        assert!(!n.is_empty() && n.len() <= 64 && v.len() <= 64, "entry {i}");
        assert!(n.iter().all(|c| !c.is_ascii_uppercase()), "entry {i}");
    }
}

/// `static_find` is a hint the encoder checks before use; it should still
/// find every entry, so the encoder compresses well.
#[test]
fn index_finds_every_entry() {
    for i in 0..99 {
        let (n, v) = static_entry(i);
        let (full, name) = static_find(n, v);
        assert!(full < 99, "entry {i}");
        assert_eq!(static_entry(full), (n, v), "entry {i}");
        assert!(name < 99 && static_entry(name).0 == n, "entry {i}");
    }
}
