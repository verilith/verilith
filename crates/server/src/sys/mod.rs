//! The trusted operating-system shim: sockets, readiness, the clock, CPU
//! pinning. Every function here is a thin wrapper over one system call and
//! is outside Verus. TRUST.md lists what the rest of the crate assumes of it.
//!
//! The interface is the same on every platform: a [`Poller`] that reports
//! readable/writable sockets by token, edge-triggered, and nonblocking
//! sockets with `read`, `writev` and `close`.
#![allow(non_camel_case_types, dead_code)]

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "linux")]
pub use linux::*;

#[cfg(target_os = "macos")]
mod macos;
#[cfg(target_os = "macos")]
pub use macos::*;

use std::io;

pub type c_int = i32;
pub type socklen_t = u32;

pub const EAGAIN_LINUX: i32 = 11;

/// One readiness event: the token the socket was registered with, and
/// whether it is readable, writable, or hung up.
#[derive(Clone, Copy, Debug, Default)]
pub struct Event {
    pub token: u64,
    pub readable: bool,
    pub writable: bool,
    pub hup: bool,
}

#[repr(C)]
pub struct iovec {
    pub iov_base: *const u8,
    pub iov_len: usize,
}

/// `struct msghdr`: Linux uses `size_t` for the lengths, macOS `int`/`socklen_t`.
#[repr(C)]
pub struct msghdr {
    pub msg_name: *mut u8,
    pub msg_namelen: socklen_t,
    pub msg_iov: *const iovec,
    #[cfg(target_os = "linux")]
    pub msg_iovlen: usize,
    #[cfg(target_os = "macos")]
    pub msg_iovlen: c_int,
    pub msg_control: *mut u8,
    #[cfg(target_os = "linux")]
    pub msg_controllen: usize,
    #[cfg(target_os = "macos")]
    pub msg_controllen: socklen_t,
    pub msg_flags: c_int,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct sockaddr_in {
    #[cfg(target_os = "macos")]
    pub sin_len: u8,
    #[cfg(target_os = "macos")]
    pub sin_family: u8,
    #[cfg(target_os = "linux")]
    pub sin_family: u16,
    pub sin_port: u16,
    pub sin_addr: u32,
    pub sin_zero: [u8; 8],
}

#[repr(C)]
pub struct timespec {
    pub tv_sec: i64,
    pub tv_nsec: i64,
}

unsafe extern "C" {
    fn socket(domain: c_int, ty: c_int, protocol: c_int) -> c_int;
    fn setsockopt(fd: c_int, level: c_int, name: c_int, val: *const u8, len: socklen_t) -> c_int;
    fn bind(fd: c_int, addr: *const sockaddr_in, len: socklen_t) -> c_int;
    fn listen(fd: c_int, backlog: c_int) -> c_int;
    fn read(fd: c_int, buf: *mut u8, n: usize) -> isize;
    fn writev(fd: c_int, iov: *const iovec, n: c_int) -> isize;
    fn sendmsg(fd: c_int, msg: *const msghdr, flags: c_int) -> isize;
    fn close(fd: c_int) -> c_int;
    fn openat(dir: c_int, path: *const std::ffi::c_char, flags: c_int, ...) -> c_int;
    fn clock_gettime(clk: c_int, ts: *mut timespec) -> c_int;
    fn time(t: *mut i64) -> i64;
}

fn cvt(r: c_int) -> io::Result<c_int> {
    if r < 0 { Err(io::Error::last_os_error()) } else { Ok(r) }
}

/// A nonblocking TCP listening socket on 127.0.0.1 or 0.0.0.0, with
/// SO_REUSEADDR, SO_REUSEPORT (one per worker on Linux), and `backlog`.
pub fn listen_tcp(addr: [u8; 4], port: u16, reuseport: bool, backlog: i32) -> io::Result<i32> {
    unsafe {
        let fd = cvt(socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK_FLAG | SOCK_CLOEXEC_FLAG, 0))?;
        set_nonblocking_cloexec(fd)?;
        let one: c_int = 1;
        cvt(setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one as *const c_int as *const u8, 4))?;
        if reuseport {
            cvt(setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one as *const c_int as *const u8, 4))?;
        }
        let sa = sockaddr_in {
            #[cfg(target_os = "macos")]
            sin_len: std::mem::size_of::<sockaddr_in>() as u8,
            sin_family: AF_INET as _,
            sin_port: port.to_be(),
            sin_addr: u32::from_ne_bytes(addr),
            sin_zero: [0; 8],
        };
        if bind(fd, &sa, std::mem::size_of::<sockaddr_in>() as socklen_t) < 0 {
            let e = io::Error::last_os_error();
            close(fd);
            return Err(e);
        }
        // Best effort: the server is correct without either.
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one as *const c_int as *const u8, 4);
        if let Some(opt) = TCP_DEFER_ACCEPT {
            let secs: c_int = 1;
            setsockopt(fd, IPPROTO_TCP, opt, &secs as *const c_int as *const u8, 4);
        }
        cvt(listen(fd, backlog))?;
        Ok(fd)
    }
}

/// Disables Nagle's algorithm: responses are written whole, once per batch.
pub fn set_nodelay(fd: i32) {
    let one: c_int = 1;
    unsafe {
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one as *const c_int as *const u8, 4);
    }
}

/// Acknowledges the next segments at once instead of delaying the ACK
/// (Linux; a no-op elsewhere). The kernel leaves quick-ACK mode by itself,
/// so a caller sets it again for as long as it wants it.
pub fn quickack(fd: i32) {
    if let Some(opt) = TCP_QUICKACK {
        let one: c_int = 1;
        unsafe {
            setsockopt(fd, IPPROTO_TCP, opt, &one as *const c_int as *const u8, 4);
        }
    }
}

/// Opens `rel` (components joined by `/`) for reading, beneath the
/// directory `dir`: on Linux with `openat2(RESOLVE_BENEATH |
/// RESOLVE_NO_MAGICLINKS)`, so no `..` or symlink resolves outside `dir`;
/// elsewhere (or before Linux 5.6) one component at a time with
/// `O_NOFOLLOW`, so no symlink is followed at all. The kernel's guarantee,
/// trusted (TRUST.md); `path.rs` proves `rel` has no `.`, `..` or empty
/// component to begin with.
pub fn open_beneath(dir: &std::fs::File, rel: &[u8]) -> io::Result<std::fs::File> {
    use std::os::fd::{AsRawFd, FromRawFd};
    let c = std::ffi::CString::new(rel).map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
    if let Some(r) = openat2_beneath(dir.as_raw_fd(), &c) {
        return r.map(|fd| unsafe { std::fs::File::from_raw_fd(fd) });
    }
    let parts: Vec<&[u8]> = rel.split(|&b| b == b'/').collect();
    let mut cur: Option<std::fs::File> = None;
    for (i, p) in parts.iter().enumerate() {
        if p.is_empty() || *p == b"." || *p == b".." {
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        }
        let c = std::ffi::CString::new(*p).map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
        let last = i + 1 == parts.len();
        let flags = O_CLOEXEC | O_NOFOLLOW | if last { 0 } else { O_DIRECTORY };
        let at = cur.as_ref().map_or(dir.as_raw_fd(), |f| f.as_raw_fd());
        let fd = unsafe { openat(at, c.as_ptr(), flags) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        cur = Some(unsafe { std::fs::File::from_raw_fd(fd) });
    }
    cur.ok_or_else(|| io::Error::from(io::ErrorKind::InvalidInput))
}

pub enum IoResult {
    /// This many bytes.
    Done(usize),
    /// The socket would block.
    WouldBlock,
    /// The peer closed (read) or the connection is broken.
    Closed,
}

/// `read(2)` into `buf`. Contract: on `Done(n)`, `n <= buf.len()`, `n > 0`,
/// and `buf[..n]` holds the bytes read.
#[inline]
pub fn read_into(fd: i32, buf: &mut [u8]) -> IoResult {
    let r = unsafe { read(fd, buf.as_mut_ptr(), buf.len()) };
    if r > 0 {
        IoResult::Done(r as usize)
    } else if r == 0 {
        IoResult::Closed
    } else {
        let e = io::Error::last_os_error();
        match e.kind() {
            io::ErrorKind::WouldBlock => IoResult::WouldBlock,
            io::ErrorKind::Interrupted => IoResult::Done(0),
            _ => IoResult::Closed,
        }
    }
}

/// `writev(2)`. Contract: on `Done(n)`, `n <=` the total length, and the
/// first `n` bytes of the slices, in order, were written.
#[inline]
pub fn write_slices(fd: i32, bufs: &[&[u8]], more: bool) -> IoResult {
    let mut iov: [iovec; 8] = unsafe { std::mem::zeroed() };
    let k = bufs.len().min(8);
    for i in 0..k {
        iov[i] = iovec { iov_base: bufs[i].as_ptr(), iov_len: bufs[i].len() };
    }
    let r = if more && MSG_MORE != 0 {
        // A head with its body to follow by sendfile: one packet, not two.
        let m = msghdr { msg_name: std::ptr::null_mut(), msg_namelen: 0, msg_iov: iov.as_ptr(), msg_iovlen: k as _, msg_control: std::ptr::null_mut(), msg_controllen: 0, msg_flags: 0 };
        unsafe { sendmsg(fd, &m, MSG_MORE) }
    } else {
        unsafe { writev(fd, iov.as_ptr(), k as c_int) }
    };
    if r >= 0 {
        IoResult::Done(r as usize)
    } else {
        let e = io::Error::last_os_error();
        match e.kind() {
            io::ErrorKind::WouldBlock => IoResult::WouldBlock,
            io::ErrorKind::Interrupted => IoResult::Done(0),
            _ => IoResult::Closed,
        }
    }
}

/// A file descriptor closed on drop.
#[derive(Debug)]
pub struct Fd(pub i32);

impl Drop for Fd {
    fn drop(&mut self) {
        close_fd(self.0);
    }
}

pub fn close_fd(fd: i32) {
    unsafe {
        close(fd);
    }
}

/// Seconds since the Unix epoch.
#[inline]
pub fn unix_time() -> i64 {
    unsafe { time(std::ptr::null_mut()) }
}
