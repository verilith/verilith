//! Linux: epoll, edge-triggered; accept4; one SO_REUSEPORT socket per worker.
use super::{c_int, cvt, Event};

#[path = "uring.rs"]
pub mod uring;
use std::io;

pub const AF_INET: c_int = 2;
pub const SOCK_STREAM: c_int = 1;
pub const SOCK_DGRAM: c_int = 2;
pub const SOL_UDP: c_int = 17;
pub const UDP_GRO: Option<c_int> = Some(104);
/// Generic segmentation offload: one `sendmsg` carries many datagrams.
pub const UDP_SEGMENT: Option<c_int> = Some(103);
/// UDP sockets with SO_REUSEPORT are balanced by the 4-tuple, so a
/// client's datagrams always reach the same worker.
pub const UDP_REUSEPORT_BALANCES: bool = true;
pub const SOCK_NONBLOCK_FLAG: c_int = 0o4000;
pub const SOCK_CLOEXEC_FLAG: c_int = 0o2000000;
pub const SOL_SOCKET: c_int = 1;
pub const SO_REUSEADDR: c_int = 2;
pub const SO_REUSEPORT: c_int = 15;
pub const SO_SNDBUF: c_int = 7;
pub const SO_RCVBUF: c_int = 8;
pub const IPPROTO_TCP: c_int = 6;
pub const IPPROTO_IP: c_int = 0;
/// IP_MTU_DISCOVER = IP_PMTUDISC_PROBE: every datagram goes with DF set
/// and is never fragmented; one larger than the interface's MTU fails
/// with EMSGSIZE. Path MTU discovery's probes need it (RFC 8899 §3).
pub const DONT_FRAGMENT: Option<(c_int, c_int)> = Some((10, 3));
pub const TCP_NODELAY: c_int = 1;
/// The kernel spreads connections across SO_REUSEPORT sockets.
pub const REUSEPORT_BALANCES: bool = true;
/// Accepted sockets inherit TCP_NODELAY from the listener.
pub const NODELAY_INHERITED: bool = true;
pub const TCP_QUICKACK: Option<c_int> = Some(12);
/// Wake `accept` only once the client has sent data (nginx's `deferred`):
/// the request arrives with the connection, one wakeup instead of two.
pub const TCP_DEFER_ACCEPT: Option<c_int> = Some(9);

pub const O_CLOEXEC: c_int = 0o2000000;
#[cfg(target_arch = "aarch64")]
pub const O_NOFOLLOW: c_int = 0o100000;
#[cfg(target_arch = "aarch64")]
pub const O_DIRECTORY: c_int = 0o40000;
#[cfg(not(target_arch = "aarch64"))]
pub const O_NOFOLLOW: c_int = 0o400000;
#[cfg(not(target_arch = "aarch64"))]
pub const O_DIRECTORY: c_int = 0o200000;

const SYS_OPENAT2: std::ffi::c_long = 437;
const SYS_EPOLL_PWAIT2: std::ffi::c_long = 441;
const RESOLVE_NO_MAGICLINKS: u64 = 0x02;
const RESOLVE_BENEATH: u64 = 0x08;

#[repr(C)]
struct OpenHow {
    flags: u64,
    mode: u64,
    resolve: u64,
}

unsafe extern "C" {
    fn syscall(n: std::ffi::c_long, ...) -> std::ffi::c_long;
}

/// `openat2(dir, path, O_RDONLY | O_CLOEXEC, RESOLVE_BENEATH |
/// RESOLVE_NO_MAGICLINKS)`: the kernel refuses any resolution, through
/// `..` or a symlink, that leaves `dir`. None if the kernel has no openat2
/// (before 5.6).
pub fn openat2_beneath(dir: c_int, path: &std::ffi::CStr) -> Option<io::Result<c_int>> {
    let how = OpenHow { flags: O_CLOEXEC as u64, mode: 0, resolve: RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS };
    let r = unsafe { syscall(SYS_OPENAT2, dir as std::ffi::c_long, path.as_ptr(), &how as *const OpenHow, std::mem::size_of::<OpenHow>()) };
    if r < 0 {
        let e = io::Error::last_os_error();
        if e.raw_os_error() == Some(38) {
            return None; // ENOSYS
        }
        return Some(Err(e));
    }
    Some(Ok(r as c_int))
}

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
    pub fn wait(&mut self, timeout_ms: i32, f: impl FnMut(Event)) -> usize {
        let n = unsafe { epoll_wait(self.ep, self.evs.as_mut_ptr(), self.evs.len() as c_int, timeout_ms) };
        self.deliver(n, f)
    }

    /// Waits up to `timeout_us` microseconds and calls `f` for each event:
    /// with epoll_pwait2 (Linux 5.11) to the microsecond, else rounded up
    /// to a millisecond.
    #[inline]
    pub fn wait_us(&mut self, timeout_us: u64, f: impl FnMut(Event)) -> usize {
        static PWAIT2: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);
        if !timeout_us.is_multiple_of(1000) && PWAIT2.load(std::sync::atomic::Ordering::Relaxed) {
            let ts = super::timespec { tv_sec: (timeout_us / 1_000_000) as i64, tv_nsec: (timeout_us % 1_000_000) as i64 * 1000 };
            let r = unsafe {
                syscall(
                    SYS_EPOLL_PWAIT2,
                    self.ep as std::ffi::c_long,
                    self.evs.as_mut_ptr(),
                    self.evs.len() as std::ffi::c_long,
                    &ts as *const super::timespec,
                    std::ptr::null::<u8>(),
                    0 as std::ffi::c_long,
                )
            };
            if r >= 0 || io::Error::last_os_error().raw_os_error() != Some(38) {
                return self.deliver(r as c_int, f);
            }
            PWAIT2.store(false, std::sync::atomic::Ordering::Relaxed);
        }
        self.wait(timeout_us.div_ceil(1000).min(i32::MAX as u64) as i32, f)
    }

    #[inline]
    fn deliver(&mut self, n: c_int, mut f: impl FnMut(Event)) -> usize {
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

unsafe extern "C" {
    fn sendfile(out_fd: c_int, in_fd: c_int, offset: *mut i64, count: usize) -> isize;
    fn memfd_create(name: *const u8, flags: u32) -> c_int;
    fn fcntl(fd: c_int, cmd: c_int, arg: c_int) -> c_int;
    fn pwrite(fd: c_int, buf: *const u8, n: usize, off: i64) -> isize;
}

/// The kernel sends file pages to the socket without copying them through
/// user memory.
pub const HAS_SENDFILE: bool = true;
pub const MSG_MORE: c_int = 0x8000;

/// `sendfile(2)` of `file[off..off + len]` to `sock`. Contract: on
/// `Done(n)`, the next `n` bytes written to the socket are `file[off..off + n]`.
pub fn sendfile_nb(sock: i32, file: i32, off: usize, len: usize) -> super::IoResult {
    let mut o = off as i64;
    let r = unsafe { sendfile(sock, file, &mut o, len) };
    if r >= 0 {
        super::IoResult::Done(r as usize)
    } else {
        match std::io::Error::last_os_error().kind() {
            std::io::ErrorKind::WouldBlock => super::IoResult::WouldBlock,
            std::io::ErrorKind::Interrupted => super::IoResult::Done(0),
            _ => super::IoResult::Closed,
        }
    }
}

/// An in-memory file holding exactly `bytes`, sealed so that nothing,
/// in this process or any other, can change, grow or shrink it: what
/// `sendfile` sends from it is what the Content-Length was computed from.
pub fn sealed_memfd(bytes: &[u8]) -> Option<super::Fd> {
    const MFD_CLOEXEC: u32 = 1;
    const MFD_ALLOW_SEALING: u32 = 2;
    const F_ADD_SEALS: c_int = 1033;
    const F_SEAL_SEAL: c_int = 1;
    const F_SEAL_SHRINK: c_int = 2;
    const F_SEAL_GROW: c_int = 4;
    const F_SEAL_WRITE: c_int = 8;
    let fd = unsafe { memfd_create(b"verilith-body\0".as_ptr(), MFD_CLOEXEC | MFD_ALLOW_SEALING) };
    if fd < 0 {
        return None;
    }
    let fd = super::Fd(fd);
    let mut at = 0;
    while at < bytes.len() {
        let r = unsafe { pwrite(fd.0, bytes[at..].as_ptr(), bytes.len() - at, at as i64) };
        if r <= 0 {
            return None;
        }
        at += r as usize;
    }
    let seals = F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE;
    if unsafe { fcntl(fd.0, F_ADD_SEALS, seals) } < 0 {
        return None;
    }
    Some(fd)
}

/// kTLS: the kernel protects what is written to a TCP socket as TLS
/// records (Linux 4.13+, TLS 1.3 from 5.1, its key updates from 6.14),
/// with the `tls` module.
pub const HAS_KTLS: bool = true;
const SOL_TLS: c_int = 282;
const TLS_TX: c_int = 1;
const TCP_ULP: c_int = 31;
const TLS_SET_RECORD_TYPE: c_int = 1;
const TLS_1_3_VERSION: u16 = 0x0304;
const TLS_CIPHER_AES_GCM_128: u16 = 51;
const TLS_CIPHER_AES_GCM_256: u16 = 52;
const TLS_CIPHER_CHACHA20_POLY1305: u16 = 54;

/// The kernel's `struct tls12_crypto_info_*` for these keys, in `info`;
/// its length, or `None` for a suite or key length the kernel has no
/// cipher for. The key and IV are secret: they are only copied, at offsets
/// that depend on the suite and the key's length, which are public
/// (`scripts/ctcheck.py` checks the machine code; see TRUST.md).
#[inline(never)]
pub fn ktls_crypto_info(suite: u16, key: &[u8], iv: &[u8; 12], seq: u64, info: &mut [u8; 56]) -> Option<usize> {
    // struct tls12_crypto_info_*: version, cipher, then (AES-GCM) the
    // explicit IV (the last 8 IV bytes), key, salt (the first 4), record
    // sequence; (ChaCha20-Poly1305) the 12-byte IV, key, record sequence.
    let cipher = match (suite, key.len()) {
        (0x1301, 16) => TLS_CIPHER_AES_GCM_128,
        (0x1302, 32) => TLS_CIPHER_AES_GCM_256,
        (0x1303, 32) => TLS_CIPHER_CHACHA20_POLY1305,
        _ => return None,
    };
    info[0..2].copy_from_slice(&TLS_1_3_VERSION.to_ne_bytes());
    info[2..4].copy_from_slice(&cipher.to_ne_bytes());
    Some(if cipher == TLS_CIPHER_CHACHA20_POLY1305 {
        info[4..16].copy_from_slice(iv);
        info[16..48].copy_from_slice(key);
        info[48..56].copy_from_slice(&seq.to_be_bytes());
        56
    } else {
        let k = key.len();
        info[4..12].copy_from_slice(&iv[4..]);
        info[12..12 + k].copy_from_slice(key);
        info[12 + k..16 + k].copy_from_slice(&iv[..4]);
        info[16 + k..24 + k].copy_from_slice(&seq.to_be_bytes());
        24 + k
    })
}

/// Gives the kernel TLS 1.3 record protection of what is sent on `sock`
/// from now on: cipher suite `suite` (0x1301-0x1303), traffic key `key`,
/// IV `iv`, the next record's sequence number `seq`. `ulp`: first attach
/// the kernel's TLS layer to the socket (the first call on a socket;
/// later calls change the keys, after a KeyUpdate). Contract: on Ok, every
/// byte later written to `sock` (`writev`, `sendfile`) goes out in
/// application-data records sealed with these keys, numbered from `seq`;
/// on Err from the first call the socket sends plaintext as before (an
/// attached TLS layer without keys passes it through). The error says
/// whether attaching the TLS layer failed (`true`: the kernel has no kTLS,
/// for instance no `tls` module) or the keys were refused (`false`: say,
/// a cipher the kernel lacks).
pub fn ktls_tx(sock: i32, suite: u16, key: &[u8], iv: &[u8; 12], seq: u64, ulp: bool) -> Result<(), (bool, io::Error)> {
    unsafe extern "C" {
        fn setsockopt(fd: c_int, level: c_int, name: c_int, val: *const u8, len: u32) -> c_int;
    }
    let mut info = [0u8; 56];
    let n = match ktls_crypto_info(suite, key, iv, seq, &mut info) {
        Some(n) => n,
        None => return Err((false, io::Error::from(io::ErrorKind::Unsupported))),
    };
    let r = (|| {
        if ulp && unsafe { setsockopt(sock, IPPROTO_TCP, TCP_ULP, b"tls".as_ptr(), 3) } < 0 {
            return Err((true, io::Error::last_os_error()));
        }
        if unsafe { setsockopt(sock, SOL_TLS, TLS_TX, info.as_ptr(), n as u32) } < 0 {
            return Err((false, io::Error::last_os_error()));
        }
        Ok(())
    })();
    for b in info.iter_mut() {
        // SAFETY: a valid byte of `info`.
        unsafe { std::ptr::write_volatile(b, 0) };
    }
    r
}

/// Under kTLS: sends `data` as a record of content type `ty` (an alert or
/// a handshake message) instead of application data. Contract: on
/// `Done(n)`, the first `n` bytes of `data` were sent, in a record of
/// that type.
pub fn send_record(sock: i32, ty: u8, data: &[u8]) -> super::IoResult {
    #[repr(C)]
    struct Cmsg {
        len: usize,
        level: c_int,
        ty: c_int,
        data: [u8; 8],
    }
    let mut c = Cmsg { len: std::mem::size_of::<usize>() + 8 + 1, level: SOL_TLS, ty: TLS_SET_RECORD_TYPE, data: [0; 8] };
    c.data[0] = ty;
    let iov = super::iovec { iov_base: data.as_ptr(), iov_len: data.len() };
    let m = super::msghdr {
        msg_name: std::ptr::null_mut(),
        msg_namelen: 0,
        msg_iov: &iov,
        msg_iovlen: 1,
        msg_control: &mut c as *mut Cmsg as *mut u8,
        msg_controllen: std::mem::size_of::<Cmsg>(),
        msg_flags: 0,
    };
    unsafe extern "C" {
        fn sendmsg(fd: c_int, msg: *const super::msghdr, flags: c_int) -> isize;
    }
    let r = unsafe { sendmsg(sock, &m, 0) };
    if r >= 0 {
        super::IoResult::Done(r as usize)
    } else {
        match io::Error::last_os_error().kind() {
            io::ErrorKind::WouldBlock => super::IoResult::WouldBlock,
            io::ErrorKind::Interrupted => super::IoResult::Done(0),
            _ => super::IoResult::Closed,
        }
    }
}
