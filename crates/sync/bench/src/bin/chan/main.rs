//! Bounded channel throughput: P senders, C receivers, blocking send/recv.
//!
//! Besides vsync and crossbeam-channel, two controls that run the channel
//! glue vsync had before that glue was verified (hand-written waiter
//! lists, a SeqCst fence and a `len()` re-check) over a different queue:
//! - `xglue`: over crossbeam-queue's ArrayQueue, to measure the glue alone;
//! - `xglue_sc`: over a copy of that queue whose stamp stores are SeqCst
//!   (chan/cbsc.rs), to measure what the SeqCst-only proofs cost.
//! xglue.rs and xglue_sc.rs are frozen copies; they differ only in the
//! queue they import.
use std::time::Instant;

#[path = "xglue.rs"]
#[allow(dead_code)]
mod xglue;

#[path = "cbsc.rs"]
#[allow(dead_code)]
mod cbsc;
#[path = "xglue_sc.rs"]
#[allow(dead_code)]
mod xglue_sc;

const N: usize = 5_000_000;

macro_rules! run {
    ($m:ident, $p:expr, $c:expr, $cap:expr) => {{
        let (s, r) = $m::bounded::<usize>($cap);
        let per = N / $p;
        let start = Instant::now();
        let mut hs = vec![];
        for k in 0..$p {
            let s = s.clone();
            hs.push(std::thread::spawn(move || {
                for i in 0..per {
                    s.send(k * per + i).unwrap();
                }
            }));
        }
        drop(s);
        let mut rs = vec![];
        for _ in 0..$c {
            let r = r.clone();
            rs.push(std::thread::spawn(move || r.iter().fold(0usize, |a, v| a.wrapping_add(v))));
        }
        drop(r);
        for h in hs { h.join().unwrap(); }
        let sum = rs.into_iter().map(|h| h.join().unwrap()).fold(0usize, |a, v| a.wrapping_add(v));
        let el = start.elapsed();
        let total = per * $p;
        assert_eq!(sum, total * (total - 1) / 2);
        el.as_nanos() as f64 / total as f64
    }};
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let which = a[1].as_str();
    let p: usize = a[2].parse().unwrap();
    let c: usize = a[3].parse().unwrap();
    let cap: usize = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(1024);
    let ns = match which {
        "vsync" => { use verilith_sync::channel as m; run!(m, p, c, cap) }
        "xglue" => { use xglue as m; run!(m, p, c, cap) }
        "xglue_sc" => { use xglue_sc as m; run!(m, p, c, cap) }
        "crossbeam" => { use crossbeam_channel as m; run!(m, p, c, cap) }
        _ => panic!(),
    };
    println!("{which}\t{p}p{c}c\tcap={cap}\t{ns:.2} ns/msg");
}
