//! SPSC throughput: one producer thread pushes N u64s, one consumer pops
//! them, each pinned to its own core. Prints ns per item.
use std::time::Instant;

const N: u64 = 50_000_000;

fn pin(core: usize) {
    let ids = core_affinity::get_core_ids().unwrap();
    core_affinity::set_for_current(ids[core % ids.len()]);
}

fn run_vsync(cap: u64) -> f64 {
    let (mut p, mut c, _) = verilith_sync::spsc::new::<u64>(cap);
    let t = std::thread::spawn(move || {
        pin(1);
        let mut i = 0;
        while i < N {
            if p.push(i).is_ok() {
                i += 1;
            } else {
                std::hint::spin_loop();
            }
        }
    });
    pin(0);
    let start = Instant::now();
    let mut sum = 0u64;
    let mut n = 0;
    while n < N {
        if let Some(v) = c.pop() {
            sum = sum.wrapping_add(v);
            n += 1;
        } else {
            std::hint::spin_loop();
        }
    }
    let el = start.elapsed();
    t.join().unwrap();
    assert_eq!(sum, N * (N - 1) / 2);
    el.as_nanos() as f64 / N as f64
}

fn run_rtrb(cap: u64) -> f64 {
    let (mut p, mut c) = rtrb::RingBuffer::<u64>::new(cap as usize);
    let t = std::thread::spawn(move || {
        pin(1);
        let mut i = 0;
        while i < N {
            if p.push(i).is_ok() {
                i += 1;
            } else {
                std::hint::spin_loop();
            }
        }
    });
    pin(0);
    let start = Instant::now();
    let mut sum = 0u64;
    let mut n = 0;
    while n < N {
        if let Ok(v) = c.pop() {
            sum = sum.wrapping_add(v);
            n += 1;
        } else {
            std::hint::spin_loop();
        }
    }
    let el = start.elapsed();
    t.join().unwrap();
    assert_eq!(sum, N * (N - 1) / 2);
    el.as_nanos() as f64 / N as f64
}

/// Batches of `B` items: `push_slice` / `pop_into`.
const B: usize = 64;

fn run_vsync_batch(cap: u64) -> f64 {
    let (mut p, mut c, _) = verilith_sync::spsc::new::<u64>(cap);
    let t = std::thread::spawn(move || {
        pin(1);
        let mut buf = [0u64; B];
        let mut next = 0u64;
        let mut start = B;
        while next < N || start < B {
            if start == B {
                for (j, x) in buf.iter_mut().enumerate() {
                    *x = next + j as u64;
                }
                next += B as u64;
                start = 0;
            }
            let k = p.push_slice(&buf[start..]);
            if k == 0 {
                std::hint::spin_loop();
            }
            start += k;
        }
    });
    pin(0);
    let start = Instant::now();
    let mut sum = 0u64;
    let mut n = 0;
    let mut out = Vec::with_capacity(B);
    while n < N {
        out.clear();
        let k = c.pop_into(&mut out, B);
        if k == 0 {
            std::hint::spin_loop();
        }
        for &v in &out {
            sum = sum.wrapping_add(v);
        }
        n += k as u64;
    }
    let el = start.elapsed();
    t.join().unwrap();
    assert_eq!(sum, N * (N - 1) / 2);
    el.as_nanos() as f64 / N as f64
}

fn run_rtrb_chunks(cap: u64) -> f64 {
    let (mut p, mut c) = rtrb::RingBuffer::<u64>::new(cap as usize);
    let t = std::thread::spawn(move || {
        pin(1);
        let mut next = 0u64;
        while next < N {
            let want = B.min(p.slots()).min((N - next) as usize);
            if want == 0 {
                std::hint::spin_loop();
                continue;
            }
            let chunk = p.write_chunk_uninit(want).unwrap();
            let n = chunk.fill_from_iter(next..next + want as u64);
            next += n as u64;
        }
    });
    pin(0);
    let start = Instant::now();
    let mut sum = 0u64;
    let mut n = 0;
    while n < N {
        let k = B.min(c.slots());
        if k == 0 {
            std::hint::spin_loop();
            continue;
        }
        let chunk = c.read_chunk(k).unwrap();
        for v in chunk.into_iter() {
            sum = sum.wrapping_add(v);
        }
        n += k as u64;
    }
    let el = start.elapsed();
    t.join().unwrap();
    assert_eq!(sum, N * (N - 1) / 2);
    el.as_nanos() as f64 / N as f64
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let which = args.get(1).map(|s| s.as_str()).unwrap_or("vsync");
    let cap: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1024);
    let ns = match which {
        "vsync" => run_vsync(cap),
        "rtrb" => run_rtrb(cap),
        "vsync-batch" => run_vsync_batch(cap),
        "rtrb-chunks" => run_rtrb_chunks(cap),
        _ => panic!("unknown"),
    };
    println!("{which}\tcap={cap}\t{ns:.2} ns/item");
}
