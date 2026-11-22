use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;
use verilith_sync::rwlock::{RwLock, RwLockWriteGuard};

const PER: u64 = if cfg!(miri) { 200 } else { 50_000 };

#[test]
fn basic() {
    let l = RwLock::new(1);
    {
        let a = l.read();
        let b = l.read();
        assert_eq!(*a + *b, 2);
        assert!(l.try_write().is_none());
        assert!(l.is_locked() && !l.is_locked_exclusive());
    }
    {
        let mut w = l.write();
        *w = 7;
        assert!(l.try_read().is_none());
        assert!(l.try_write().is_none());
        assert!(l.is_locked_exclusive());
    }
    assert!(!l.is_locked());
    assert_eq!(l.into_inner(), 7);
}

#[test]
fn downgrade_keeps_writers_out() {
    let l = RwLock::new(0);
    let mut w = l.write();
    *w = 3;
    let r = RwLockWriteGuard::downgrade(w);
    assert_eq!(*r, 3);
    assert!(l.try_write().is_none());
    let r2 = l.try_read().unwrap();
    assert_eq!(*r2, 3);
    drop(r);
    drop(r2);
    assert!(l.try_write().is_some());
}

#[test]
fn readers_and_writers_stress() {
    // Writers keep two fields equal; readers must never see them differ.
    let l = Arc::new(RwLock::new((0u64, 0u64)));
    let reads = Arc::new(AtomicUsize::new(0));
    let mut hs = vec![];
    for _ in 0..3 {
        let l = l.clone();
        hs.push(std::thread::spawn(move || {
            for _ in 0..PER {
                let mut g = l.write();
                g.0 += 1;
                g.1 += 1;
            }
        }));
    }
    for _ in 0..3 {
        let l = l.clone();
        let reads = reads.clone();
        hs.push(std::thread::spawn(move || {
            for _ in 0..PER {
                let g = l.read();
                assert_eq!(g.0, g.1);
                reads.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    assert_eq!(*l.read(), (3 * PER, 3 * PER));
    assert_eq!(reads.load(Ordering::Relaxed) as u64, 3 * PER);
}

#[test]
fn long_holds_park_and_wake() {
    let l = Arc::new(RwLock::new(0));
    let mut hs = vec![];
    for i in 0..6 {
        let l = l.clone();
        hs.push(std::thread::spawn(move || {
            for _ in 0..20 {
                if i % 2 == 0 {
                    let mut g = l.write();
                    *g += 1;
                    std::thread::sleep(Duration::from_micros(200));
                } else {
                    let _g = l.read();
                    std::thread::sleep(Duration::from_micros(200));
                }
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    assert_eq!(*l.read(), 60);
}

#[test]
fn timeouts() {
    let l = Arc::new(RwLock::new(()));
    let r = l.read();
    assert!(l.try_write_for(Duration::from_millis(30)).is_none());
    // The timed-out writer may leave new readers blocked only until the
    // current readers leave.
    drop(r);
    assert!(l.try_read_for(Duration::from_millis(1000)).is_some());
    let w = l.write();
    assert!(l.try_read_for(Duration::from_millis(30)).is_none());
    let l2 = l.clone();
    let h = std::thread::spawn(move || l2.try_read_for(Duration::from_secs(10)).is_some());
    std::thread::sleep(Duration::from_millis(20));
    drop(w);
    assert!(h.join().unwrap());
}

#[test]
fn drops_value_once() {
    let v = Arc::new(());
    {
        let _l = RwLock::new(v.clone());
        assert_eq!(Arc::strong_count(&v), 2);
    }
    assert_eq!(Arc::strong_count(&v), 1);
}
