use std::sync::Arc;
use std::time::{Duration, Instant};
use verilith_sync::mutex::Mutex;

#[test]
fn basic() {
    let m = Mutex::new(5);
    {
        let mut g = m.lock();
        *g += 1;
        assert!(m.is_locked());
        assert!(m.try_lock().is_none());
    }
    assert!(!m.is_locked());
    assert_eq!(*m.try_lock().unwrap(), 6);
    assert_eq!(m.into_inner(), 6);
}

#[test]
fn counter_stress() {
    let m = Arc::new(Mutex::new(0u64));
    let threads = 8;
    let per = if cfg!(miri) { 200 } else { 100_000 };
    let hs: Vec<_> = (0..threads)
        .map(|_| {
            let m = m.clone();
            std::thread::spawn(move || {
                for _ in 0..per {
                    *m.lock() += 1;
                }
            })
        })
        .collect();
    for h in hs {
        h.join().unwrap();
    }
    assert_eq!(*m.lock(), threads * per);
}

#[test]
fn long_holds_park_and_wake() {
    // Holding the lock across sleeps forces waiters past the spin phase.
    let m = Arc::new(Mutex::new(Vec::new()));
    let hs: Vec<_> = (0..4)
        .map(|i| {
            let m = m.clone();
            std::thread::spawn(move || {
                for j in 0..20 {
                    let mut g = m.lock();
                    g.push((i, j));
                    std::thread::sleep(Duration::from_micros(200));
                }
            })
        })
        .collect();
    for h in hs {
        h.join().unwrap();
    }
    assert_eq!(m.lock().len(), 80);
}

#[test]
fn timeouts() {
    let m = Arc::new(Mutex::new(()));
    let g = m.lock();
    let t = Instant::now();
    assert!(m.try_lock_for(Duration::from_millis(50)).is_none());
    assert!(t.elapsed() >= Duration::from_millis(50));
    let m2 = m.clone();
    let h = std::thread::spawn(move || m2.try_lock_for(Duration::from_secs(10)).is_some());
    std::thread::sleep(Duration::from_millis(20));
    drop(g);
    assert!(h.join().unwrap());
}

#[test]
fn drops_value_once() {
    let v = Arc::new(());
    {
        let _m = Mutex::new(v.clone());
        assert_eq!(Arc::strong_count(&v), 2);
    }
    assert_eq!(Arc::strong_count(&v), 1);
    let m = Mutex::new(v.clone());
    let inner = m.into_inner();
    assert_eq!(Arc::strong_count(&v), 2);
    drop(inner);
    assert_eq!(Arc::strong_count(&v), 1);
}
