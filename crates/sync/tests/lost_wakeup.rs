//! A receiver that is about to park must not miss a message sent while it
//! registers (and likewise for a sender waiting on a full channel). Under
//! Miri's weak-memory emulation this exercises the store-buffering pattern
//! between the waiter's registration and the queue's tail/head update.
use std::thread;


#[test]
fn recv_wakeup_not_lost() {
    let rounds = if cfg!(miri) { 300 } else { 2000 };
    for round in 0..rounds {
        let (tx, rx) = verilith_sync::channel::bounded::<u32>(4);
        let r = thread::spawn(move || rx.recv().unwrap());
        for _ in 0..round % 300 {
            thread::yield_now();
        }
        tx.send(7).unwrap();
        // Keep the sender alive so the receiver can only return by being woken.
        assert_eq!(r.join().unwrap(), 7);
        drop(tx);
    }
}

#[test]
fn send_wakeup_not_lost() {
    let rounds = if cfg!(miri) { 300 } else { 2000 };
    for round in 0..rounds {
        let (tx, rx) = verilith_sync::channel::bounded::<u32>(1);
        tx.send(1).unwrap();
        let s = thread::spawn(move || tx.send(2).unwrap());
        for _ in 0..round % 300 {
            thread::yield_now();
        }
        assert_eq!(rx.recv().unwrap(), 1);
        s.join().unwrap();
        assert_eq!(rx.recv().unwrap(), 2);
    }
}
