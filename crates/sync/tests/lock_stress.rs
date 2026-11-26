//! Every kind of lock call at once, timed ones included, so that sleepers
//! time out while others wake them: the runs must finish (no lost wakeup,
//! no hint left set) with the data consistent.
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use verilith_sync::mutex::Mutex;
use verilith_sync::rwlock::{RwLock, RwLockWriteGuard};

fn rounds() -> u64 {
    if cfg!(miri) { 50 } else { 20_000 }
}

/// Holds the lock a while now and then, so that others park.
fn hold(i: u64) {
    if i % 64 == 0 {
        thread::sleep(Duration::from_micros(20));
    } else if i % 8 == 0 {
        thread::yield_now();
    }
}

#[test]
fn rwlock_mixed_calls() {
    let l = Arc::new(RwLock::new((0u64, 0u64)));
    let hs: Vec<_> = (0..8u64)
        .map(|me| {
            let l = l.clone();
            thread::spawn(move || {
                let mut done = 0u64;
                for i in 0..rounds() {
                    match (i + me) % 6 {
                        0 => {
                            let mut w = l.write();
                            w.0 += 1;
                            hold(i);
                            w.1 += 1;
                            done += 1;
                        }
                        1 => {
                            let r = l.read();
                            hold(i);
                            assert_eq!(r.0, r.1);
                        }
                        2 => {
                            if let Some(mut w) = l.try_write_for(Duration::from_micros(50)) {
                                w.0 += 1;
                                w.1 += 1;
                                done += 1;
                            }
                        }
                        3 => {
                            if let Some(r) = l.try_read_for(Duration::from_micros(50)) {
                                assert_eq!(r.0, r.1);
                            }
                        }
                        4 => {
                            let mut w = l.write();
                            w.0 += 1;
                            hold(i);
                            w.1 += 1;
                            done += 1;
                            let r = RwLockWriteGuard::downgrade(w);
                            assert_eq!(r.0, r.1);
                        }
                        _ => {
                            if let Some(r) = l.try_read() {
                                assert_eq!(r.0, r.1);
                            }
                            if let Some(mut w) = l.try_write() {
                                w.0 += 1;
                                w.1 += 1;
                                done += 1;
                            }
                        }
                    }
                }
                done
            })
        })
        .collect();
    let total: u64 = hs.into_iter().map(|h| h.join().unwrap()).sum();
    let r = l.read();
    assert_eq!(*r, (total, total));
    drop(r);
    // Nobody is left holding or waiting: the lock is free for both kinds.
    assert!(l.try_write().is_some());
}

#[test]
fn mutex_mixed_calls() {
    let m = Arc::new(Mutex::new(0u64));
    let hs: Vec<_> = (0..8u64)
        .map(|me| {
            let m = m.clone();
            thread::spawn(move || {
                let mut done = 0u64;
                for i in 0..rounds() {
                    match (i + me) % 3 {
                        0 => {
                            let mut g = m.lock();
                            hold(i);
                            *g += 1;
                            done += 1;
                        }
                        1 => {
                            if let Some(mut g) = m.try_lock_for(Duration::from_micros(50)) {
                                *g += 1;
                                done += 1;
                            }
                        }
                        _ => {
                            if let Some(mut g) = m.try_lock() {
                                *g += 1;
                                done += 1;
                            }
                        }
                    }
                }
                done
            })
        })
        .collect();
    let total: u64 = hs.into_iter().map(|h| h.join().unwrap()).sum();
    assert_eq!(*m.lock(), total);
    assert!(!m.is_locked());
}
