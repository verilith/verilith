use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use verilith_sync::array_queue::ArrayQueue;

#[test]
fn fifo_single_thread() {
    for cap in [1usize, 2, 3, 7, 8, 100] {
        let q = ArrayQueue::<usize>::new(cap);
        for round in 0..5 {
            for i in 0..cap {
                assert!(q.push(round * 1000 + i).is_ok());
            }
            assert_eq!(q.push(99), Err(99));
            for i in 0..cap {
                assert_eq!(q.pop(), Some(round * 1000 + i));
            }
            assert_eq!(q.pop(), None);
        }
    }
}

#[test]
fn mpmc_every_value_once() {
    const P: usize = 4;
    const C: usize = 4;
    const N: usize = if cfg!(miri) { 500 } else { 200_000 };
    let q = Arc::new(ArrayQueue::<usize>::new(64));
    let seen: Arc<Vec<AtomicUsize>> = Arc::new((0..P * N).map(|_| AtomicUsize::new(0)).collect());
    let done = Arc::new(AtomicUsize::new(0));
    let mut hs = vec![];
    for p in 0..P {
        let q = q.clone();
        hs.push(thread::spawn(move || {
            for i in 0..N {
                let mut v = p * N + i;
                loop {
                    match q.push(v) {
                        Ok(()) => break,
                        Err(back) => {
                            v = back;
                            thread::yield_now();
                        }
                    }
                }
            }
        }));
    }
    for _ in 0..C {
        let q = q.clone();
        let seen = seen.clone();
        let done = done.clone();
        hs.push(thread::spawn(move || {
            // Per producer, values must come out in the order pushed.
            let mut last = vec![None::<usize>; P];
            while done.load(Ordering::SeqCst) < P * N {
                if let Some(v) = q.pop() {
                    let (p, i) = (v / N, v % N);
                    if let Some(l) = last[p] {
                        assert!(i > l, "producer {p}: {i} after {l}");
                    }
                    last[p] = Some(i);
                    assert_eq!(seen[v].fetch_add(1, Ordering::SeqCst), 0);
                    done.fetch_add(1, Ordering::SeqCst);
                }
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    assert!(seen.iter().all(|s| s.load(Ordering::SeqCst) == 1));
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
        let q = ArrayQueue::new(5);
        for _ in 0..5 {
            assert!(q.push(Counted(drops.clone())).is_ok());
        }
        // Wrap around once so head and tail are mid-buffer.
        drop(q.pop());
        drop(q.pop());
        drop(q.pop());
        assert!(q.push(Counted(drops.clone())).is_ok());
        assert_eq!(drops.load(Ordering::SeqCst), 3);
    }
    assert_eq!(drops.load(Ordering::SeqCst), 6);
}
