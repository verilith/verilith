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
    fn recvmsg(fd: c_int, msg: *mut msghdr, flags: c_int) -> isize;
    fn recvfrom(fd: c_int, buf: *mut u8, n: usize, flags: c_int, addr: *mut sockaddr_in, len: *mut socklen_t) -> isize;
    fn close(fd: c_int) -> c_int;
    fn openat(dir: c_int, path: *const std::ffi::c_char, flags: c_int, ...) -> c_int;
    fn clock_gettime(clk: c_int, ts: *mut timespec) -> c_int;
    fn time(t: *mut i64) -> i64;
    fn connect(fd: c_int, addr: *const sockaddr_in, len: socklen_t) -> c_int;
    fn getsockopt(fd: c_int, level: c_int, name: c_int, val: *mut u8, len: *mut socklen_t) -> c_int;
    fn pipe(fds: *mut c_int) -> c_int;
    fn write(fd: c_int, buf: *const u8, n: usize) -> isize;
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

/// A nonblocking TCP socket connecting to `addr:port`, with TCP_NODELAY:
/// the connection completes (or fails) later, when the socket turns
/// writable; [`take_error`] then says which.
pub fn connect_nb(addr: [u8; 4], port: u16) -> io::Result<i32> {
    unsafe {
        let fd = cvt(socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK_FLAG | SOCK_CLOEXEC_FLAG, 0))?;
        if let Err(e) = set_nonblocking_cloexec(fd) {
            close(fd);
            return Err(e);
        }
        let one: c_int = 1;
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one as *const c_int as *const u8, 4);
        let sa = sockaddr_in {
            #[cfg(target_os = "macos")]
            sin_len: std::mem::size_of::<sockaddr_in>() as u8,
            sin_family: AF_INET as _,
            sin_port: port.to_be(),
            sin_addr: u32::from_ne_bytes(addr),
            sin_zero: [0; 8],
        };
        if connect(fd, &sa, std::mem::size_of::<sockaddr_in>() as socklen_t) < 0 {
            let e = io::Error::last_os_error();
            if e.raw_os_error() != Some(EINPROGRESS) {
                close(fd);
                return Err(e);
            }
        }
        Ok(fd)
    }
}

/// The socket's pending error (`SO_ERROR`), clearing it: `None` once a
/// nonblocking connect has succeeded.
pub fn take_error(fd: i32) -> Option<i32> {
    let mut v: c_int = 0;
    let mut len: socklen_t = 4;
    let r = unsafe { getsockopt(fd, SOL_SOCKET, SO_ERROR, &mut v as *mut c_int as *mut u8, &mut len) };
    if r < 0 {
        return Some(io::Error::last_os_error().raw_os_error().unwrap_or(-1));
    }
    if v == 0 { None } else { Some(v) }
}

/// A pipe whose ends are both nonblocking: a thread wakes a worker by
/// writing a byte to the second, which the worker's poller watches the
/// first for.
pub fn wake_pipe() -> io::Result<(i32, i32)> {
    let mut fds: [c_int; 2] = [0; 2];
    cvt(unsafe { pipe(fds.as_mut_ptr()) })?;
    for &fd in &fds {
        set_nonblocking(fd)?;
    }
    Ok((fds[0], fds[1]))
}

/// Writes one byte (a wakeup). A full pipe already holds one.
pub fn wake(fd: i32) {
    let b = 1u8;
    unsafe {
        write(fd, &b, 1);
    }
}

/// Reads everything waiting on a nonblocking descriptor, discarding it.
pub fn drain(fd: i32) {
    let mut b = [0u8; 64];
    while unsafe { read(fd, b.as_mut_ptr(), b.len()) } > 0 {}
}

/// A nonblocking UDP socket bound to `addr:port`, with SO_REUSEPORT if
/// `reuseport` (one per worker on Linux), and large kernel buffers.
pub fn bind_udp(addr: [u8; 4], port: u16, reuseport: bool) -> io::Result<i32> {
    unsafe {
        let fd = cvt(socket(AF_INET, SOCK_DGRAM | SOCK_NONBLOCK_FLAG | SOCK_CLOEXEC_FLAG, 0))?;
        set_nonblocking_cloexec(fd)?;
        let one: c_int = 1;
        cvt(setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one as *const c_int as *const u8, 4))?;
        if reuseport {
            cvt(setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &one as *const c_int as *const u8, 4))?;
        }
        // Best effort: SO_RCVBUF and SO_SNDBUF, 4 MiB (capped by the
        // kernel's rmem_max and wmem_max).
        let big: c_int = 4 << 20;
        setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &big as *const c_int as *const u8, 4);
        setsockopt(fd, SOL_SOCKET, SO_SNDBUF, &big as *const c_int as *const u8, 4);
        // Never fragment: a datagram the path cannot carry is lost, so
        // QUIC's path MTU probes find what the path carries (RFC 9000
        // §14.1, RFC 8899 §3).
        if let Some((opt, v)) = DONT_FRAGMENT {
            cvt(setsockopt(fd, IPPROTO_IP, opt, &v as *const c_int as *const u8, 4))?;
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
        // Generic receive offload: the kernel may hand over several
        // datagrams of one flow in one read (see `recv_gro`).
        if let Some(opt) = UDP_GRO {
            setsockopt(fd, SOL_UDP, opt, &one as *const c_int as *const u8, 4);
        }
        Ok(fd)
    }
}

/// `recvfrom(2)`: one datagram into `buf`, and its sender. Contract: on
/// `Some((n, ip, port))`, `n <= buf.len()` and `buf[..n]` holds it (cut
/// short if it was longer). `None`: nothing more to read now.
#[inline]
pub fn recv_from(fd: i32, buf: &mut [u8]) -> Option<(usize, [u8; 4], u16)> {
    loop {
        let mut sa: sockaddr_in = unsafe { std::mem::zeroed() };
        let mut len = std::mem::size_of::<sockaddr_in>() as socklen_t;
        let r = unsafe { recvfrom(fd, buf.as_mut_ptr(), buf.len(), 0, &mut sa, &mut len) };
        if r >= 0 {
            if sa.sin_family as c_int != AF_INET {
                continue;
            }
            return Some(((r as usize).min(buf.len()), sa.sin_addr.to_ne_bytes(), u16::from_be(sa.sin_port)));
        }
        if io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
            return None;
        }
    }
}

/// One read from a UDP socket with receive offload: `Some((n, ip, port,
/// seg))` wrote `buf[..n]`, which holds datagrams of `seg` bytes back to
/// back from one sender (the last may be shorter; `seg == n` for a single
/// datagram). The memory may be uninitialized (a `BytesMut`'s spare
/// capacity); the first `n` bytes are initialized on return.
#[inline]
pub fn recv_gro(fd: i32, buf: &mut [std::mem::MaybeUninit<u8>]) -> Option<(usize, [u8; 4], u16, usize)> {
    loop {
        let mut sa: sockaddr_in = unsafe { std::mem::zeroed() };
        let iov = iovec { iov_base: buf.as_mut_ptr() as *const u8, iov_len: buf.len() };
        let mut cmsg = [0u64; 8];
        let mut m = msghdr {
            msg_name: &mut sa as *mut sockaddr_in as *mut u8,
            msg_namelen: std::mem::size_of::<sockaddr_in>() as socklen_t,
            msg_iov: &iov,
            msg_iovlen: 1,
            msg_control: cmsg.as_mut_ptr() as *mut u8,
            msg_controllen: std::mem::size_of_val(&cmsg) as _,
            msg_flags: 0,
        };
        let r = unsafe { recvmsg(fd, &mut m, 0) };
        if r < 0 {
            if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return None;
        }
        if sa.sin_family as c_int != AF_INET {
            continue;
        }
        let n = (r as usize).min(buf.len());
        let mut seg = n;
        // Walk the control messages: { size_t len; int level; int type; data }.
        if let Some(opt) = UDP_GRO {
            let base = cmsg.as_ptr() as *const u8;
            let total = (m.msg_controllen as usize).min(std::mem::size_of_val(&cmsg));
            let hdr = std::mem::size_of::<usize>() + 8;
            let mut at = 0usize;
            while at + hdr <= total {
                let (len, level, ty) = unsafe {
                    (
                        *(base.add(at) as *const usize),
                        *(base.add(at + std::mem::size_of::<usize>()) as *const c_int),
                        *(base.add(at + std::mem::size_of::<usize>() + 4) as *const c_int),
                    )
                };
                if len < hdr || at + len > total {
                    break;
                }
                if level == SOL_UDP && ty == opt && len >= hdr + 2 {
                    let v = unsafe { std::ptr::read_unaligned(base.add(at + hdr) as *const u16) } as usize;
                    if v > 0 {
                        seg = v;
                    }
                }
                at += (len + 7) & !7;
            }
        }
        return Some((n, sa.sin_addr.to_ne_bytes(), u16::from_be(sa.sin_port), seg));
    }
}

/// [`recv_from`] into memory not yet initialized (a `BytesMut`'s spare
/// capacity). Contract: on `Some((n, ..))` the first `n` bytes are
/// initialized and hold the datagram.
#[inline]
pub fn recv_from_uninit(fd: i32, buf: &mut [std::mem::MaybeUninit<u8>]) -> Option<(usize, [u8; 4], u16)> {
    // SAFETY: recvfrom only writes to the buffer, and `u8` has no
    // invalid values; nothing reads the bytes past what it wrote.
    let b = unsafe { std::slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u8, buf.len()) };
    recv_from(fd, b)
}

/// Sends `buf` to `ip:port` as datagrams of `segment` bytes (the last may
/// be shorter): one `sendmsg` with UDP_SEGMENT where the kernel has it
/// and `*gso` is still true, else one per datagram. A kernel that refuses
/// segmentation turns `*gso` off. Datagrams the socket has no room for are
/// dropped, as a network would: QUIC recovers them. Returns false if any
/// was dropped.
pub fn send_to(fd: i32, buf: &[u8], ip: [u8; 4], port: u16, segment: usize, gso: &mut bool) -> bool {
    let sa = sockaddr_in {
        #[cfg(target_os = "macos")]
        sin_len: std::mem::size_of::<sockaddr_in>() as u8,
        sin_family: AF_INET as _,
        sin_port: port.to_be(),
        sin_addr: u32::from_ne_bytes(ip),
        sin_zero: [0; 8],
    };
    let segment = segment.max(1);
    let send = |b: &[u8], seg: Option<u16>| -> isize {
        let iov = iovec { iov_base: b.as_ptr(), iov_len: b.len() };
        // struct cmsghdr { size_t len; int level; int type; } + a u16,
        // padded to CMSG_SPACE(2) = 24 bytes on 64-bit Linux.
        let mut cmsg = [0u64; 3];
        let mut m = msghdr {
            msg_name: &sa as *const sockaddr_in as *mut u8,
            msg_namelen: std::mem::size_of::<sockaddr_in>() as socklen_t,
            msg_iov: &iov,
            msg_iovlen: 1,
            msg_control: std::ptr::null_mut(),
            msg_controllen: 0,
            msg_flags: 0,
        };
        if let (Some(s), Some(opt)) = (seg, UDP_SEGMENT) {
            let p = cmsg.as_mut_ptr() as *mut u8;
            unsafe {
                *(p as *mut usize) = std::mem::size_of::<usize>() + 8 + 2;
                *(p.add(std::mem::size_of::<usize>()) as *mut c_int) = SOL_UDP;
                *(p.add(std::mem::size_of::<usize>() + 4) as *mut c_int) = opt;
                *(p.add(std::mem::size_of::<usize>() + 8) as *mut u16) = s;
            }
            m.msg_control = p;
            m.msg_controllen = (std::mem::size_of::<usize>() + 16) as _;
        }
        loop {
            let r = unsafe { sendmsg(fd, &m, 0) };
            if r >= 0 || io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                return r;
            }
        }
    };
    if buf.len() > segment && *gso && UDP_SEGMENT.is_some() && segment <= u16::MAX as usize && std::mem::size_of::<usize>() == 8 {
        if send(buf, Some(segment as u16)) >= 0 {
            return true;
        }
        let e = io::Error::last_os_error();
        if e.kind() == io::ErrorKind::WouldBlock {
            return false;
        }
        // EIO or EINVAL: no segmentation offload on this path.
        *gso = false;
    }
    let mut ok = true;
    for b in buf.chunks(segment) {
        if send(b, None) < 0 {
            ok = false;
            if io::Error::last_os_error().kind() == io::ErrorKind::WouldBlock {
                break;
            }
        }
    }
    ok
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
pub use crate::out::Fd;

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
