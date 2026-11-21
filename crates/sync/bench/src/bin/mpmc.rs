//! MPMC throughput: P producers and C consumers move N u64s in total
//! through a bounded queue. Prints ns per item (wall time / N).
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

const N: u64 = 20_000_000;

trait Q: Send + Sync + 'static {
    fn new(cap: usize) -> Self;
    fn push(&self, v: u64) -> bool;
    fn pop(&self) -> Option<u64>;
}

impl Q for verilith_sync::array_queue::ArrayQueue<u64> {
    fn new(cap: usize) -> Self { verilith_sync::array_queue::ArrayQueue::new(cap) }
    #[inline] fn push(&self, v: u64) -> bool { verilith_sync::array_queue::ArrayQueue::push(self, v).is_ok() }
    #[inline] fn pop(&self) -> Option<u64> { verilith_sync::array_queue::ArrayQueue::pop(self) }
}

impl Q for crossbeam_queue::ArrayQueue<u64> {
    fn new(cap: usize) -> Self { crossbeam_queue::ArrayQueue::new(cap) }
    #[inline] fn push(&self, v: u64) -> bool { crossbeam_queue::ArrayQueue::push(self, v).is_ok() }
    #[inline] fn pop(&self) -> Option<u64> { crossbeam_queue::ArrayQueue::pop(self) }
}

fn run<T: Q>(p: usize, c: usize, cap: usize) -> f64 {
    let q = Arc::new(T::new(cap));
    let sum = Arc::new(AtomicU64::new(0));
    let per = N / p as u64;
    let total = per * p as u64;
    let got = Arc::new(AtomicU64::new(0));
    let start = Instant::now();
    let mut hs = vec![];
    for k in 0..p {
        let q = q.clone();
        hs.push(std::thread::spawn(move || {
            for i in 0..per {
                let v = k as u64 * per + i;
                while !q.push(v) {
                    std::hint::spin_loop();
                }
            }
        }));
    }
    for _ in 0..c {
        let (q, sum, got) = (q.clone(), sum.clone(), got.clone());
        hs.push(std::thread::spawn(move || {
            let mut local = 0u64;
            let mut n = 0u64;
            loop {
                if let Some(v) = q.pop() {
                    local = local.wrapping_add(v);
                    n += 1;
                    if n == 1024 {
                        n = 0;
                        if got.fetch_add(1024, Ordering::Relaxed) + 1024 >= total { break; }
                    }
                } else {
                    // Publish what we have before deciding we are done, or
                    // two consumers can each wait for the other's count.
                    if n > 0 {
                        got.fetch_add(n, Ordering::Relaxed);
                        n = 0;
                    }
                    if got.load(Ordering::Relaxed) >= total {
                        break;
                    }
                    std::hint::spin_loop();
                }
            }
            got.fetch_add(n, Ordering::Relaxed);
            sum.fetch_add(local, Ordering::Relaxed);
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let el = start.elapsed();
    assert_eq!(sum.load(Ordering::Relaxed), total * (total - 1) / 2);
    el.as_nanos() as f64 / total as f64
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let which = a[1].as_str();
    let p: usize = a[2].parse().unwrap();
    let c: usize = a[3].parse().unwrap();
    let cap: usize = a.get(4).and_then(|s| s.parse().ok()).unwrap_or(1024);
    let ns = match which {
        "vsync" => run::<verilith_sync::array_queue::ArrayQueue<u64>>(p, c, cap),
        "crossbeam" => run::<crossbeam_queue::ArrayQueue<u64>>(p, c, cap),
        _ => panic!(),
    };
    println!("{which}\t{p}p{c}c\tcap={cap}\t{ns:.2} ns/item");
}
