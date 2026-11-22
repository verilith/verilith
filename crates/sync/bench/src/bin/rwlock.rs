//! RwLock throughput: T threads; every Wth operation writes, the rest read.
//! W=0 means reads only.
use std::sync::Arc;
use std::time::Instant;

const TOTAL: u64 = 4_000_000;

macro_rules! run {
    ($new:expr, $t:expr, $w:expr, $read:ident, $write:ident) => {{
        let l = Arc::new($new);
        let per = TOTAL / $t;
        let start = Instant::now();
        let hs: Vec<_> = (0..$t)
            .map(|_| {
                let l = l.clone();
                std::thread::spawn(move || {
                    let mut acc = 0u64;
                    for i in 0..per {
                        if $w != 0 && i % $w == 0 {
                            let mut g = l.$write();
                            *g = std::hint::black_box(*g + 1);
                        } else {
                            acc = acc.wrapping_add(*l.$read());
                        }
                    }
                    std::hint::black_box(acc);
                })
            })
            .collect();
        for h in hs {
            h.join().unwrap();
        }
        start.elapsed().as_nanos() as f64 / (per * $t) as f64
    }};
}

struct Std(std::sync::RwLock<u64>);
impl Std {
    fn read(&self) -> std::sync::RwLockReadGuard<'_, u64> {
        self.0.read().unwrap()
    }
    fn write(&self) -> std::sync::RwLockWriteGuard<'_, u64> {
        self.0.write().unwrap()
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let which = a[1].as_str();
    let t: u64 = a[2].parse().unwrap();
    let w: u64 = a[3].parse().unwrap();
    let ns = match which {
        "vsync" => run!(verilith_sync::rwlock::RwLock::new(0u64), t, w, read, write),
        "parking_lot" => run!(parking_lot::RwLock::new(0u64), t, w, read, write),
        "std" => run!(Std(std::sync::RwLock::new(0u64)), t, w, read, write),
        _ => panic!(),
    };
    println!("{which}\t{t}t\tw={w}\t{ns:.2} ns/op");
}
