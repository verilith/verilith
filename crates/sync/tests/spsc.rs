use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use verilith_sync::spsc;

#[test]
fn fifo_single_thread() {
    let (mut p, mut c, _) = spsc::new::<u32>(3);
    assert!(c.pop().is_none());
    assert!(p.push(1).is_ok());
    assert!(p.push(2).is_ok());
    assert!(p.push(3).is_ok());
    assert_eq!(p.push(4), Err(4));
    assert_eq!(c.pop(), Some(1));
    assert!(p.push(4).is_ok());
    assert_eq!(c.pop(), Some(2));
    assert_eq!(c.pop(), Some(3));
    assert_eq!(c.pop(), Some(4));
    assert_eq!(c.pop(), None);
}

#[test]
fn two_threads_in_order() {
    const N: u64 = if cfg!(miri) { 2_000 } else { 2_000_000 };
    let (mut p, mut c, _) = spsc::new::<u64>(64);
    let t = thread::spawn(move || {
        let mut i = 0;
        while i < N {
            if p.push(i).is_ok() {
                i += 1;
            }
        }
    });
    let mut next = 0;
    while next < N {
        if let Some(v) = c.pop() {
            assert_eq!(v, next);
            next += 1;
        }
    }
    t.join().unwrap();
}

struct Counted(Arc<AtomicUsize>);
impl Drop for Counted {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn drops_leftovers() {
    let drops = Arc::new(AtomicUsize::new(0));
    {
        let (mut p, mut c, _) = spsc::new::<Counted>(4);
        for _ in 0..4 {
            assert!(p.push(Counted(drops.clone())).is_ok());
        }
        drop(c.pop());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        drop(c);
        // Pushed after the consumer is gone: dropped with the producer.
        assert!(p.push(Counted(drops.clone())).is_ok());
    }
    assert_eq!(drops.load(Ordering::SeqCst), 5);
}

#[test]
fn drops_leftovers_producer_first() {
    let drops = Arc::new(AtomicUsize::new(0));
    let (mut p, mut c, _) = spsc::new::<Counted>(8);
    for _ in 0..6 {
        assert!(p.push(Counted(drops.clone())).is_ok());
    }
    drop(p);
    // The consumer can still drain what the producer left.
    drop(c.pop());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    drop(c);
    assert_eq!(drops.load(Ordering::SeqCst), 6);
}

#[test]
fn drops_leftovers_racing() {
    let rounds = if cfg!(miri) { 20 } else { 2000 };
    let drops = Arc::new(AtomicUsize::new(0));
    let mut made = 0;
    for r in 0..rounds {
        let (mut p, mut c, _) = spsc::new::<Counted>(4);
        let d = drops.clone();
        let t = std::thread::spawn(move || {
            for _ in 0..(r % 7) {
                // A rejected value comes back and is dropped here.
                let _ = p.push(Counted(d.clone()));
            }
        });
        for _ in 0..(r % 3) {
            drop(c.pop());
        }
        drop(c);
        t.join().unwrap();
        made += r % 7;
    }
    // Every value was dropped exactly once: popped, rejected, or left in
    // the queue for whichever side left last.
    assert_eq!(drops.load(Ordering::SeqCst), made);
}

#[test]
fn batches() {
    let (mut p, mut c, _) = spsc::new::<u32>(4);
    assert_eq!(p.push_slice(&[1, 2, 3]), 3);
    assert_eq!(p.push_slice(&[4, 5, 6]), 1);
    assert_eq!(p.push_slice(&[7]), 0);
    let mut out = Vec::new();
    assert_eq!(c.pop_into(&mut out, 2), 2);
    assert_eq!(out, [1, 2]);
    assert_eq!(p.push_slice(&[5, 6, 7]), 2);
    assert_eq!(c.pop_into(&mut out, 100), 4);
    assert_eq!(out, [1, 2, 3, 4, 5, 6]);
    assert_eq!(c.pop_into(&mut out, 100), 0);
}

#[test]
fn batches_threaded() {
    const N: u64 = if cfg!(miri) { 2_000 } else { 2_000_000 };
    let (mut p, mut c, _) = spsc::new::<u64>(64);
    let h = std::thread::spawn(move || {
        let data: Vec<u64> = (0..N).collect();
        let mut sent = 0;
        while sent < data.len() {
            let end = (sent + 17).min(data.len());
            sent += p.push_slice(&data[sent..end]);
        }
    });
    let mut out = Vec::with_capacity(N as usize);
    while (out.len() as u64) < N {
        c.pop_into(&mut out, 23);
    }
    h.join().unwrap();
    assert!(out.iter().copied().eq(0..N));
}

/// `Tid` is `!Send`; the queue's endpoints opt back in explicitly.
#[test]
fn endpoints_are_send() {
    fn assert_send<T: Send>() {}
    assert_send::<verilith_sync::spsc::Producer<u64>>();
    assert_send::<verilith_sync::spsc::Consumer<u64>>();
    assert_send::<verilith_sync::spsc::Producer<String>>();
}
