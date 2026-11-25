//! A lock nested at offset 0 of another lock's data shares its address.
//! The parking lot is keyed by address, so if both locks parked under the
//! lock's own address, the inner mutex's unlock could wake a waiter of the
//! outer RwLock instead of its own, and the mutex waiter would sleep
//! forever next to an unlocked mutex. Both lock types now park under the
//! address of their lock word, which no other live lock shares.
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::{Duration, Instant};
use verilith_sync::mutex::Mutex;
use verilith_sync::rwlock::RwLock;

#[test]
fn mutex_inside_rwlock_wakes_its_own_waiter() {
    let l = Arc::new(RwLock::new(Mutex::new(0u64)));
    {
        let g = l.read();
        let m: &Mutex<u64> = &g;
        assert_eq!(&*l as *const _ as usize, m as *const _ as usize, "layout changed: the test no longer nests at offset 0");
    }
    let got = Arc::new(AtomicBool::new(false));
    let b = Arc::new(Barrier::new(3));
    // A reader holds the inner mutex while the others queue up.
    let (l2, b2) = (l.clone(), b.clone());
    let holder = thread::spawn(move || {
        let g = l2.read();
        let m = g.lock();
        b2.wait();
        thread::sleep(Duration::from_millis(300));
        drop(m);
        thread::sleep(Duration::from_millis(100));
        drop(g);
    });
    // A second reader parks on the inner mutex, after the writer has
    // parked on the RwLock, so the writer is first in the bucket.
    let (l1, b1, got1) = (l.clone(), b.clone(), got.clone());
    let waiter = thread::spawn(move || {
        let g = l1.read();
        b1.wait();
        thread::sleep(Duration::from_millis(150));
        *g.lock() += 1;
        got1.store(true, Ordering::SeqCst);
    });
    b.wait();
    let lw = l.clone();
    let writer = thread::spawn(move || {
        *lw.write().lock() += 1;
    });
    let start = Instant::now();
    while !got.load(Ordering::SeqCst) {
        assert!(start.elapsed() < Duration::from_secs(5), "the mutex waiter was never woken");
        thread::sleep(Duration::from_millis(10));
    }
    holder.join().unwrap();
    waiter.join().unwrap();
    writer.join().unwrap();
    assert_eq!(*l.read().lock(), 2);
}
