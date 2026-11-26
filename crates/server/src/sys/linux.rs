//! Linux: epoll, edge-triggered; accept4; one SO_REUSEPORT socket per worker.
use super::{c_int, cvt, Event};
use std::io;

pub const AF_INET: c_int = 2;
pub const SOCK_STREAM: c_int = 1;
pub const SOCK_NONBLOCK_FLAG: c_int = 0o4000;
pub const SOCK_CLOEXEC_FLAG: c_int = 0o2000000;
pub const SOL_SOCKET: c_int = 1;
pub const SO_REUSEADDR: c_int = 2;
pub const SO_REUSEPORT: c_int = 15;
pub const IPPROTO_TCP: c_int = 6;
pub const TCP_NODELAY: c_int = 1;
/// The kernel spreads connections across SO_REUSEPORT sockets.
pub const REUSEPORT_BALANCES: bool = true;
/// Accepted sockets inherit TCP_NODELAY from the listener.
pub const NODELAY_INHERITED: bool = true;
/// Wake `accept` only once the client has sent data (nginx's `deferred`):
/// the request arrives with the connection, one wakeup instead of two.
pub const TCP_DEFER_ACCEPT: Option<c_int> = Some(9);

const EPOLL_CLOEXEC: c_int = 0o2000000;
const EPOLL_CTL_ADD: c_int = 1;
const EPOLL_CTL_DEL: c_int = 2;
const EPOLLIN: u32 = 0x1;
const EPOLLOUT: u32 = 0x4;
const EPOLLERR: u32 = 0x8;
const EPOLLHUP: u32 = 0x10;
const EPOLLRDHUP: u32 = 0x2000;
const EPOLLET: u32 = 1 << 31;

#[cfg_attr(target_arch = "x86_64", repr(C, packed))]
#[cfg_attr(not(target_arch = "x86_64"), repr(C))]
#[derive(Clone, Copy)]
struct epoll_event {
    events: u32,
    data: u64,
}

unsafe extern "C" {
    fn epoll_create1(flags: c_int) -> c_int;
    fn epoll_ctl(epfd: c_int, op: c_int, fd: c_int, ev: *mut epoll_event) -> c_int;
    fn epoll_wait(epfd: c_int, evs: *mut epoll_event, max: c_int, timeout: c_int) -> c_int;
    fn accept4(fd: c_int, addr: *mut u8, len: *mut u32, flags: c_int) -> c_int;
    fn sched_setaffinity(pid: c_int, size: usize, mask: *const u64) -> c_int;
    fn signal(sig: c_int, handler: usize) -> usize;
}

pub(super) fn set_nonblocking_cloexec(_fd: i32) -> io::Result<()> {
    Ok(()) // socket() and accept4() take the flags directly
}

/// Writes to a closed socket return EPIPE instead of killing the process.
pub fn ignore_sigpipe() {
    unsafe {
        signal(13, 1);
    }
}

/// Accepts one connection, nonblocking and close-on-exec. `None` when no
/// connection is waiting (or on a transient error).
#[inline]
pub fn accept_nb(fd: i32) -> Option<i32> {
    let r = unsafe { accept4(fd, std::ptr::null_mut(), std::ptr::null_mut(), SOCK_NONBLOCK_FLAG | SOCK_CLOEXEC_FLAG) };
    if r < 0 { None } else { Some(r) }
}

/// Pins the calling thread to one CPU.
pub fn pin_to_cpu(cpu: usize) {
    let mut mask = [0u64; 16];
    if cpu < 1024 {
        mask[cpu / 64] |= 1 << (cpu % 64);
        unsafe {
            sched_setaffinity(0, std::mem::size_of_val(&mask), mask.as_ptr());
        }
    }
}

/// The CPUs this process may run on.
pub fn allowed_cpus() -> Vec<usize> {
    unsafe extern "C" {
        fn sched_getaffinity(pid: c_int, size: usize, mask: *mut u64) -> c_int;
    }
    let mut mask = [0u64; 16];
    let mut out = Vec::new();
    unsafe {
        if sched_getaffinity(0, std::mem::size_of_val(&mask), mask.as_mut_ptr()) == 0 {
            for c in 0..1024 {
                if mask[c / 64] & (1 << (c % 64)) != 0 {
                    out.push(c);
                }
            }
        }
    }
    out
}

pub struct Poller {
    ep: c_int,
    evs: Vec<epoll_event>,
}

impl Poller {
    pub fn new(cap: usize) -> io::Result<Poller> {
        let ep = cvt(unsafe { epoll_create1(EPOLL_CLOEXEC) })?;
        Ok(Poller { ep, evs: vec![epoll_event { events: 0, data: 0 }; cap] })
    }

    /// Watches `fd` for readability and writability, edge-triggered.
    pub fn add(&self, fd: i32, token: u64, write_too: bool) -> io::Result<()> {
        let mut ev = epoll_event {
            events: EPOLLIN | EPOLLRDHUP | EPOLLET | if write_too { EPOLLOUT } else { 0 },
            data: token,
        };
        cvt(unsafe { epoll_ctl(self.ep, EPOLL_CTL_ADD, fd, &mut ev) }).map(|_| ())
    }

    pub fn remove(&self, fd: i32) {
        let mut ev = epoll_event { events: 0, data: 0 };
        unsafe {
            epoll_ctl(self.ep, EPOLL_CTL_DEL, fd, &mut ev);
        }
    }

    /// Waits up to `timeout_ms` (-1: forever) and calls `f` for each event.
    #[inline]
    pub fn wait(&mut self, timeout_ms: i32, mut f: impl FnMut(Event)) -> usize {
        let n = unsafe { epoll_wait(self.ep, self.evs.as_mut_ptr(), self.evs.len() as c_int, timeout_ms) };
        if n <= 0 {
            return 0;
        }
        for i in 0..n as usize {
            let e = self.evs[i];
            let bits = e.events;
            f(Event {
                token: e.data,
                readable: bits & (EPOLLIN | EPOLLERR | EPOLLHUP | EPOLLRDHUP) != 0,
                writable: bits & (EPOLLOUT | EPOLLERR | EPOLLHUP) != 0,
                hup: bits & (EPOLLERR | EPOLLHUP) != 0,
            });
        }
        n as usize
    }
}
