//! macOS: kqueue with EV_CLEAR (edge-triggered); a listening socket shared
//! by the workers, since SO_REUSEPORT does not balance connections here.
use super::{c_int, cvt, Event};
use std::io;

pub const AF_INET: c_int = 2;
pub const SOCK_STREAM: c_int = 1;
pub const SOCK_DGRAM: c_int = 2;
pub const SOL_UDP: c_int = 17;
pub const UDP_GRO: Option<c_int> = None;
pub const UDP_SEGMENT: Option<c_int> = None;
pub const UDP_REUSEPORT_BALANCES: bool = false;
pub const SOCK_NONBLOCK_FLAG: c_int = 0;
pub const SOCK_CLOEXEC_FLAG: c_int = 0;
pub const SOL_SOCKET: c_int = 0xffff;
pub const SO_REUSEADDR: c_int = 0x4;
pub const SO_REUSEPORT: c_int = 0x200;
pub const SO_SNDBUF: c_int = 0x1001;
pub const SO_RCVBUF: c_int = 0x1002;
pub const SO_ERROR: c_int = 0x1007;
pub const EINPROGRESS: c_int = 36;
pub const IPPROTO_TCP: c_int = 6;
pub const IPPROTO_IP: c_int = 0;
/// IP_DONTFRAG: datagrams go with DF set, never fragmented, as path MTU
/// discovery's probes need (RFC 8899 §3).
pub const DONT_FRAGMENT: Option<(c_int, c_int)> = Some((28, 1));
pub const TCP_NODELAY: c_int = 1;
const SO_NOSIGPIPE: c_int = 0x1022;
/// SO_REUSEPORT on macOS sends every connection to the last socket bound.
pub const REUSEPORT_BALANCES: bool = false;
pub const NODELAY_INHERITED: bool = false;
pub const TCP_QUICKACK: Option<c_int> = None;
pub const TCP_DEFER_ACCEPT: Option<c_int> = None;

pub const O_CLOEXEC: c_int = 0x1000000;
pub const O_NOFOLLOW: c_int = 0x100;
pub const O_DIRECTORY: c_int = 0x100000;

/// No openat2 here: [`super::open_beneath`] walks the components.
pub fn openat2_beneath(_dir: c_int, _path: &std::ffi::CStr) -> Option<io::Result<c_int>> {
    None
}

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

pub(super) fn set_nonblocking(fd: i32) -> io::Result<()> {
    unsafe {
        let fl = cvt(fcntl(fd, 3))?; // F_GETFL
        cvt(fcntl(fd, 4, fl | 4))?; // F_SETFL, O_NONBLOCK
        cvt(fcntl(fd, 2, 1))?; // F_SETFD, FD_CLOEXEC
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

/// A poller's descriptor, to register sockets with it from elsewhere on
/// its thread (see `crate::reactor`).
#[derive(Clone, Copy, Debug)]
pub struct PollHandle(c_int);

impl PollHandle {
    pub fn add(self, fd: i32, token: u64, write_too: bool) -> io::Result<()> {
        let ch = [kev(fd, EVFILT_READ, EV_ADD | EV_CLEAR, token), kev(fd, EVFILT_WRITE, EV_ADD | EV_CLEAR, token)];
        let n = if write_too { 2 } else { 1 };
        cvt(unsafe { kevent(self.0, ch.as_ptr(), n, std::ptr::null_mut(), 0, std::ptr::null()) }).map(|_| ())
    }

    pub fn remove(self, _fd: i32) {
        // Closing the descriptor removes its kevents.
    }
}

impl Poller {
    pub fn new(cap: usize) -> io::Result<Poller> {
        let kq = cvt(unsafe { kqueue() })?;
        Ok(Poller { kq, evs: vec![kev(0, 0, 0, 0); cap] })
    }

    pub fn handle(&self) -> PollHandle {
        PollHandle(self.kq)
    }

    pub fn add(&self, fd: i32, token: u64, write_too: bool) -> io::Result<()> {
        self.handle().add(fd, token, write_too)
    }

    pub fn remove(&self, fd: i32) {
        self.handle().remove(fd)
    }

    /// Waits up to `timeout_us` microseconds, rounded up to a millisecond.
    #[inline]
    pub fn wait_us(&mut self, timeout_us: u64, f: impl FnMut(Event)) -> usize {
        self.wait(timeout_us.div_ceil(1000).min(i32::MAX as u64) as i32, f)
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

/// No kTLS on macOS.
pub const HAS_KTLS: bool = false;

pub fn ktls_tx(_sock: i32, _suite: u16, _key: &[u8], _iv: &[u8; 12], _seq: u64, _ulp: bool) -> Result<(), (bool, std::io::Error)> {
    Err((true, std::io::Error::from(std::io::ErrorKind::Unsupported)))
}

pub fn send_record(_sock: i32, _ty: u8, _data: &[u8]) -> super::IoResult {
    super::IoResult::Closed
}
