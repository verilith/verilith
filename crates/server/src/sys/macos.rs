//! macOS: kqueue with EV_CLEAR (edge-triggered); a listening socket shared
//! by the workers, since SO_REUSEPORT does not balance connections here.
use super::{c_int, cvt, Event};
use std::io;

pub const AF_INET: c_int = 2;
pub const SOCK_STREAM: c_int = 1;
pub const SOCK_NONBLOCK_FLAG: c_int = 0;
pub const SOCK_CLOEXEC_FLAG: c_int = 0;
pub const SOL_SOCKET: c_int = 0xffff;
pub const SO_REUSEADDR: c_int = 0x4;
pub const SO_REUSEPORT: c_int = 0x200;
pub const IPPROTO_TCP: c_int = 6;
pub const TCP_NODELAY: c_int = 1;
const SO_NOSIGPIPE: c_int = 0x1022;
/// SO_REUSEPORT on macOS sends every connection to the last socket bound.
pub const REUSEPORT_BALANCES: bool = false;
pub const NODELAY_INHERITED: bool = false;
pub const TCP_QUICKACK: Option<c_int> = None;
pub const TCP_DEFER_ACCEPT: Option<c_int> = None;

const EVFILT_READ: i16 = -1;
const EVFILT_WRITE: i16 = -2;
const EV_ADD: u16 = 0x1;
const EV_DELETE: u16 = 0x2;
const EV_CLEAR: u16 = 0x20;
const EV_EOF: u16 = 0x8000;
const EV_ERROR: u16 = 0x4000;

#[repr(C)]
#[derive(Clone, Copy)]
struct kevent_t {
    ident: usize,
    filter: i16,
    flags: u16,
    fflags: u32,
    data: isize,
    udata: *mut u8,
}

unsafe extern "C" {
    fn kqueue() -> c_int;
    fn kevent(kq: c_int, changes: *const kevent_t, nchanges: c_int, events: *mut kevent_t, nevents: c_int,
              timeout: *const super::timespec) -> c_int;
    fn accept(fd: c_int, addr: *mut u8, len: *mut u32) -> c_int;
    fn fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
    fn setsockopt(fd: c_int, level: c_int, name: c_int, val: *const u8, len: u32) -> c_int;
    fn signal(sig: c_int, handler: usize) -> usize;
}

pub(super) fn set_nonblocking_cloexec(fd: i32) -> io::Result<()> {
    unsafe {
        let fl = cvt(fcntl(fd, 3))?; // F_GETFL
        cvt(fcntl(fd, 4, fl | 4))?; // F_SETFL, O_NONBLOCK
        cvt(fcntl(fd, 2, 1))?; // F_SETFD, FD_CLOEXEC
        let one: c_int = 1;
        setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one as *const c_int as *const u8, 4);
    }
    Ok(())
}

pub fn ignore_sigpipe() {
    unsafe {
        signal(13, 1);
    }
}

#[inline]
pub fn accept_nb(fd: i32) -> Option<i32> {
    let r = unsafe { accept(fd, std::ptr::null_mut(), std::ptr::null_mut()) };
    if r < 0 {
        return None;
    }
    if set_nonblocking_cloexec(r).is_err() {
        super::close_fd(r);
        return None;
    }
    Some(r)
}

/// macOS cannot pin a thread to a CPU; the workers ask for the
/// user-interactive QoS class instead, which keeps them on performance cores.
pub fn pin_to_cpu(_cpu: usize) {
    unsafe extern "C" {
        fn pthread_set_qos_class_self_np(qos: u32, rel: c_int) -> c_int;
    }
    unsafe {
        pthread_set_qos_class_self_np(0x21, 0);
    }
}

pub fn allowed_cpus() -> Vec<usize> {
    (0..std::thread::available_parallelism().map_or(1, |n| n.get())).collect()
}

pub struct Poller {
    kq: c_int,
    evs: Vec<kevent_t>,
}

fn kev(fd: i32, filter: i16, flags: u16, token: u64) -> kevent_t {
    kevent_t { ident: fd as usize, filter, flags, fflags: 0, data: 0, udata: token as usize as *mut u8 }
}

impl Poller {
    pub fn new(cap: usize) -> io::Result<Poller> {
        let kq = cvt(unsafe { kqueue() })?;
        Ok(Poller { kq, evs: vec![kev(0, 0, 0, 0); cap] })
    }

    pub fn add(&self, fd: i32, token: u64, write_too: bool) -> io::Result<()> {
        let ch = [kev(fd, EVFILT_READ, EV_ADD | EV_CLEAR, token), kev(fd, EVFILT_WRITE, EV_ADD | EV_CLEAR, token)];
        let n = if write_too { 2 } else { 1 };
        cvt(unsafe { kevent(self.kq, ch.as_ptr(), n, std::ptr::null_mut(), 0, std::ptr::null()) }).map(|_| ())
    }

    pub fn remove(&self, _fd: i32) {
        // Closing the descriptor removes its kevents.
    }

    #[inline]
    pub fn wait(&mut self, timeout_ms: i32, mut f: impl FnMut(Event)) -> usize {
        let ts = super::timespec { tv_sec: (timeout_ms / 1000) as i64, tv_nsec: ((timeout_ms % 1000) as i64) * 1_000_000 };
        let tp = if timeout_ms < 0 { std::ptr::null() } else { &ts as *const _ };
        let n = unsafe { kevent(self.kq, std::ptr::null(), 0, self.evs.as_mut_ptr(), self.evs.len() as c_int, tp) };
        if n <= 0 {
            return 0;
        }
        for i in 0..n as usize {
            let e = self.evs[i];
            let hup = e.flags & (EV_EOF | EV_ERROR) != 0;
            f(Event {
                token: e.udata as usize as u64,
                readable: e.filter == EVFILT_READ || hup,
                writable: e.filter == EVFILT_WRITE || hup,
                hup: e.flags & EV_ERROR != 0,
            });
        }
        n as usize
    }
}

/// macOS's `sendfile` has another signature and no sealed memory files;
/// bodies are written from memory.
pub const HAS_SENDFILE: bool = false;
pub const MSG_MORE: c_int = 0;

pub fn sendfile_nb(_sock: i32, _file: i32, _off: usize, _len: usize) -> super::IoResult {
    super::IoResult::Closed
}

pub fn sealed_memfd(_bytes: &[u8]) -> Option<super::Fd> {
    None
}
