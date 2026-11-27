//! `reclog::RecLog`: each packet's records come back once, from its token.
use verilith_quic::reclog::{pack, unpack, RecLog};

#[test]
fn records_come_back_once_per_packet() {
    let mut log = RecLog::new();
    let mut tokens = Vec::new();
    for p in 0..2000u64 {
        let start = log.next_index();
        let n = 1 + p % 7;
        for j in 0..n {
            assert!(log.push((p, j)));
        }
        tokens.push(pack(start, n));
    }
    // Every packet reported twice (acknowledged after being declared lost),
    // in a scrambled order.
    let mut seen = 0;
    for round in 0..2 {
        for i in 0..tokens.len() {
            let p = (i * 769 + round) % tokens.len();
            let (start, n) = unpack(tokens[p]);
            for k in start..start + n {
                if let Some((q, _)) = log.take(k) {
                    assert_eq!(q, p as u64);
                    seen += 1;
                }
            }
            log.trim();
        }
    }
    assert_eq!(seen, (0..2000u64).map(|p| 1 + p % 7).sum::<u64>());
    assert_eq!(log.get(0), None);
}
