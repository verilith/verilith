//! Session tickets (`TicketKeys`, libcrux's ChaCha20-Poly1305): a ticket
//! opens to the state it sealed, appended after what `out` already holds,
//! and nothing else opens: a changed byte anywhere, another server's keys,
//! a truncated ticket.
use verilith_tls_aws_lc::{TicketKeys, TICKET_OVERHEAD};

#[test]
fn a_ticket_opens_to_its_state_and_nothing_else_opens() {
    let keys = TicketKeys::new(3600);
    for n in [0usize, 1, 15, 16, 17, 200, 1000] {
        let state: Vec<u8> = (0..n).map(|i| (i * 7) as u8).collect();
        let mut t = b"prefix".to_vec();
        assert!(keys.seal(&state, &mut t));
        let t = t[6..].to_vec();
        assert_eq!(t.len(), n + TICKET_OVERHEAD);
        let mut out = b"kept".to_vec();
        assert!(keys.open(&t, &mut out));
        assert_eq!(&out[..4], b"kept");
        assert_eq!(&out[4..], &state[..]);
        for i in 0..t.len() {
            let mut bad = t.clone();
            bad[i] ^= 0x01;
            let mut out = b"kept".to_vec();
            assert!(!keys.open(&bad, &mut out), "byte {i} of {n}");
            assert_eq!(out, b"kept");
        }
        let mut out = Vec::new();
        assert!(!keys.open(&t[..t.len() - 1], &mut out));
        assert!(out.is_empty());
    }
    let mut t = Vec::new();
    assert!(keys.seal(b"state", &mut t));
    let other = TicketKeys::new(3600);
    let mut out = Vec::new();
    assert!(!other.open(&t, &mut out));
    assert!(!keys.open(&t[..TICKET_OVERHEAD - 1], &mut out));
    assert!(out.is_empty());
}
