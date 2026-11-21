//! A global parking lot: threads sleep keyed by an address, as in
//! parking_lot_core, so a lock needs no space for its own wait queue.
//!
//! Not verified. It decides only when a thread sleeps and wakes, never
//! which thread owns a lock (the verified lock state does that), so a bug
//! here could cause a hang but not a data race.
use std::sync::atomic::{AtomicBool, Ordering::SeqCst};
use std::sync::{Arc, Mutex};
use std::thread::Thread;
use std::time::Instant;

struct Waiter {
    key: usize,
    thread: Thread,
    notified: AtomicBool,
}

#[repr(align(128))]
struct Bucket {
    list: Mutex<Vec<Arc<Waiter>>>,
}

const BUCKETS: usize = 64;

static TABLE: [Bucket; BUCKETS] = [const { Bucket { list: Mutex::new(Vec::new()) } }; BUCKETS];

#[inline]
fn bucket(key: usize) -> &'static Bucket {
    // Fibonacci hashing of the address.
    &TABLE[(key.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (usize::BITS - 6)) as usize]
}

/// Sleeps on `key` if `validate()` holds, until woken by `unpark_*` on the
/// same key or until the deadline. `validate` runs with the bucket locked,
/// so an unpark that follows a state change `validate` would see cannot be
/// missed. Returns false if `validate` failed or the deadline passed.
pub fn park(key: usize, validate: impl FnOnce() -> bool, deadline: Option<Instant>) -> bool {
    let b = bucket(key);
    let me = Arc::new(Waiter { key, thread: std::thread::current(), notified: AtomicBool::new(false) });
    {
        let mut list = b.list.lock().unwrap();
        if !validate() {
            return false;
        }
        list.push(me.clone());
    }
    while !me.notified.load(SeqCst) {
        match deadline {
            None => std::thread::park(),
            Some(d) => {
                let now = Instant::now();
                if now >= d {
                    let mut list = b.list.lock().unwrap();
                    if let Some(i) = list.iter().position(|w| Arc::ptr_eq(w, &me)) {
                        list.swap_remove(i);
                        return false;
                    }
                    // Woken concurrently with the timeout: count it as woken.
                    return true;
                }
                std::thread::park_timeout(d - now);
            }
        }
    }
    true
}

/// Wakes up to `n` threads parked on `key`. Returns how many were woken.
pub fn unpark(key: usize, n: usize) -> usize {
    let b = bucket(key);
    let mut woken = Vec::new();
    {
        let mut list = b.list.lock().unwrap();
        let mut i = 0;
        while i < list.len() && woken.len() < n {
            if list[i].key == key {
                woken.push(list.remove(i));
            } else {
                i += 1;
            }
        }
    }
    for w in &woken {
        w.notified.store(true, SeqCst);
        w.thread.unpark();
    }
    woken.len()
}
