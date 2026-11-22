//! The vsync SPSC algorithm written in plain Rust, with the index stores
//! either SeqCst (what vsync's proofs model) or Release (what rtrb uses),
//! and the refresh of the other side's index as a load or as an RMW.
//! Isolates the cost of the memory ordering from everything else.
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

const N: u64 = 50_000_000;

#[repr(align(128))]
struct Pad(AtomicU64);

struct Rb {
    head: Pad,
    tail: Pad,
    buf: Box<[UnsafeCell<MaybeUninit<u64>>]>,
}
unsafe impl Sync for Rb {}

fn pin(core: usize) {
    let ids = core_affinity::get_core_ids().unwrap();
    core_affinity::set_for_current(ids[core % ids.len()]);
}

fn run(st: Ordering, ld: Ordering, rmw: bool) -> f64 {
    let cap = 1024u64;
    let rb = Arc::new(Rb {
        head: Pad(AtomicU64::new(0)),
        tail: Pad(AtomicU64::new(0)),
        buf: (0..cap).map(|_| UnsafeCell::new(MaybeUninit::uninit())).collect(),
    });
    let rb2 = rb.clone();
    let t = std::thread::spawn(move || {
        pin(1);
        let (mut tail, mut idx, mut limit) = (0u64, 0u64, cap);
        let mut i = 0;
        while i < N {
            if tail == limit {
                let h = if rmw { rb2.head.0.fetch_add(0, Ordering::AcqRel) } else { rb2.head.0.load(ld) };
                if h + cap == limit { std::hint::spin_loop(); continue; }
                limit = h + cap;
            }
            unsafe { (*rb2.buf[idx as usize].get()).write(i); }
            tail += 1;
            rb2.tail.0.store(tail, st);
            idx = if idx + 1 == cap { 0 } else { idx + 1 };
            i += 1;
        }
    });
    pin(0);
    let start = Instant::now();
    let (mut head, mut idx, mut tc) = (0u64, 0u64, 0u64);
    let mut sum = 0u64;
    let mut n = 0;
    while n < N {
        if head == tc {
            let t = if rmw { rb.tail.0.fetch_add(0, Ordering::AcqRel) } else { rb.tail.0.load(ld) };
            if t == tc { std::hint::spin_loop(); continue; }
            tc = t;
        }
        let v = unsafe { (*rb.buf[idx as usize].get()).assume_init_read() };
        head += 1;
        rb.head.0.store(head, st);
        idx = if idx + 1 == cap { 0 } else { idx + 1 };
        sum = sum.wrapping_add(v);
        n += 1;
    }
    let el = start.elapsed();
    t.join().unwrap();
    assert_eq!(sum, N * (N - 1) / 2);
    el.as_nanos() as f64 / N as f64
}

fn main() {
    let which = std::env::args().nth(1).unwrap_or("sc".into());
    let ns = match which.as_str() {
        "sc" => run(Ordering::SeqCst, Ordering::SeqCst, false),
        "rel" => run(Ordering::Release, Ordering::Acquire, false),
        // Release stores, and the index refresh as a read-modify-write,
        // which always reads the latest value.
        "rmw" => run(Ordering::Release, Ordering::Acquire, true),
        _ => panic!(),
    };
    println!("plain-{which}\t{ns:.2} ns/item");
}
