//! Mutex throughput: T threads each take the lock and do a little work
//! inside it, K times. T=1 measures the uncontended path.
use std::sync::Arc;
use std::time::Instant;

const TOTAL: u64 = 4_000_000;

macro_rules! run {
    ($new:expr, $lock:ident, $t:expr, $work:expr) => {{
        let m = Arc::new($new);
        let per = TOTAL / $t;
        let start = Instant::now();
        let hs: Vec<_> = (0..$t)
            .map(|_| {
                let m = m.clone();
                std::thread::spawn(move || {
                    for _ in 0..per {
                        let mut g = m.$lock();
                        for _ in 0..$work {
                            *g = std::hint::black_box(*g + 1);
                        }
                    }
                })
            })
            .collect();
        for h in hs {
            h.join().unwrap();
        }
        let el = start.elapsed();
        el.as_nanos() as f64 / (per * $t) as f64
    }};
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let which = a[1].as_str();
    let t: u64 = a[2].parse().unwrap();
    let work: u64 = a.get(3).and_then(|s| s.parse().ok()).unwrap_or(1);
    let ns = match which {
        "vsync" => run!(verilith_sync::mutex::Mutex::new(0u64), lock, t, work),
        "parking_lot" => run!(parking_lot::Mutex::new(0u64), lock, t, work),
        "std" => {
            struct M(std::sync::Mutex<u64>);
            impl M {
                fn lock(&self) -> std::sync::MutexGuard<'_, u64> {
                    self.0.lock().unwrap()
                }
            }
            run!(M(std::sync::Mutex::new(0u64)), lock, t, work)
        }
        _ => panic!(),
    };
    println!("{which}\t{t}t\twork={work}\t{ns:.2} ns/lock");
}
