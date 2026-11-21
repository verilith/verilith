use std::thread;
use std::time::{Duration, Instant};
use verilith_sync::channel::*;

#[test]
fn smoke() {
    let (s, r) = bounded(1);
    s.send(7).unwrap();
    assert_eq!(r.try_recv(), Ok(7));
    s.send(8).unwrap();
    assert_eq!(r.recv(), Ok(8));
    assert_eq!(r.try_recv(), Err(TryRecvError::Empty));
    assert_eq!(r.recv_timeout(Duration::from_millis(10)), Err(RecvTimeoutError::Timeout));
}

#[test]
fn full_and_timeout() {
    let (s, r) = bounded(2);
    s.send(1).unwrap();
    s.send(2).unwrap();
    assert!(s.try_send(3).unwrap_err().is_full());
    assert!(s.send_timeout(3, Duration::from_millis(10)).unwrap_err().is_timeout());
    assert_eq!(s.len(), 2);
    assert!(s.is_full());
    assert_eq!(r.recv(), Ok(1));
    s.send(3).unwrap();
    assert_eq!(r.try_iter().collect::<Vec<_>>(), vec![2, 3]);
}

#[test]
fn disconnect_receivers() {
    let (s, r) = bounded::<i32>(4);
    drop(r);
    assert_eq!(s.send(1), Err(SendError(1)));
    assert!(s.try_send(2).unwrap_err().is_disconnected());
}

#[test]
fn disconnect_senders_drains_first() {
    let (s, r) = bounded(4);
    s.send(1).unwrap();
    s.send(2).unwrap();
    drop(s);
    assert_eq!(r.recv(), Ok(1));
    assert_eq!(r.recv(), Ok(2));
    assert_eq!(r.recv(), Err(RecvError));
    assert_eq!(r.try_recv(), Err(TryRecvError::Disconnected));
}

#[test]
fn blocked_receiver_wakes_on_send() {
    let (s, r) = bounded(1);
    let t = thread::spawn(move || r.recv());
    thread::sleep(Duration::from_millis(50));
    s.send(5).unwrap();
    assert_eq!(t.join().unwrap(), Ok(5));
}

#[test]
fn blocked_receiver_wakes_on_disconnect() {
    let (s, r) = bounded::<i32>(1);
    let t = thread::spawn(move || r.recv());
    thread::sleep(Duration::from_millis(50));
    drop(s);
    assert_eq!(t.join().unwrap(), Err(RecvError));
}

#[test]
fn blocked_sender_wakes_on_recv() {
    let (s, r) = bounded(1);
    s.send(1).unwrap();
    let t = thread::spawn(move || s.send(2));
    thread::sleep(Duration::from_millis(50));
    assert_eq!(r.recv(), Ok(1));
    assert_eq!(t.join().unwrap(), Ok(()));
    assert_eq!(r.recv(), Ok(2));
}

#[test]
fn mpmc_stress() {
    const P: usize = 4;
    const N: usize = if cfg!(miri) { 500 } else { 100_000 };
    let (s, r) = bounded(16);
    let mut hs = vec![];
    for p in 0..P {
        let s = s.clone();
        hs.push(thread::spawn(move || {
            for i in 0..N {
                s.send(p * N + i).unwrap();
            }
        }));
    }
    drop(s);
    let mut rs = vec![];
    for _ in 0..3 {
        let r = r.clone();
        rs.push(thread::spawn(move || r.iter().collect::<Vec<_>>()));
    }
    let mut all: Vec<usize> = r.iter().collect();
    for h in hs {
        h.join().unwrap();
    }
    for t in rs {
        all.extend(t.join().unwrap());
    }
    all.sort();
    assert_eq!(all, (0..P * N).collect::<Vec<_>>());
}

#[test]
fn deadline() {
    let (_s, r) = bounded::<()>(1);
    let start = Instant::now();
    assert!(r.recv_timeout(Duration::from_millis(100)).unwrap_err().is_timeout());
    assert!(start.elapsed() >= Duration::from_millis(100));
}
