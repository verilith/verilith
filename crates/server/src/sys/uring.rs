//! Linux io_uring, the second event-loop backend (DESIGN.md, "I/O model"):
//! a submission and a completion ring shared with the kernel, so a whole
//! loop turn of receives, sends and accepts costs one system call.
//!
//! Trusted, like the rest of `sys`: a thin layer over `io_uring_setup(2)`,
//! `io_uring_enter(2)` and the ring layout in `<linux/io_uring.h>`. The
//! contract the worker relies on is the kernel's: memory named by a
//! submitted entry (a receive buffer, a `msghdr` and its `iovec`s) stays
//! valid and unmoved until that entry's completion arrives, and exactly one
//! completion arrives per entry (or several, flagged `more`, for a
//! multishot entry), carrying the entry's `user_data`.
use crate::sys::{c_int, iovec, msghdr};
use std::io;
use std::sync::atomic::{AtomicU32, Ordering};

const SYS_IO_URING_SETUP: std::ffi::c_long = 425;
const SYS_IO_URING_ENTER: std::ffi::c_long = 426;

const IORING_OFF_SQ_RING: i64 = 0;
const IORING_OFF_CQ_RING: i64 = 0x8000000;
const IORING_OFF_SQES: i64 = 0x10000000;

const IORING_SETUP_CQSIZE: u32 = 1 << 3;
const IORING_SETUP_CLAMP: u32 = 1 << 4;
const IORING_SETUP_SUBMIT_ALL: u32 = 1 << 7;
const IORING_SETUP_COOP_TASKRUN: u32 = 1 << 8;
const IORING_SETUP_SINGLE_ISSUER: u32 = 1 << 12;
const IORING_SETUP_DEFER_TASKRUN: u32 = 1 << 13;

const IORING_FEAT_SINGLE_MMAP: u32 = 1 << 0;
const IORING_FEAT_NODROP: u32 = 1 << 1;
const IORING_FEAT_EXT_ARG: u32 = 1 << 8;

const IORING_ENTER_GETEVENTS: u32 = 1 << 0;
const IORING_ENTER_EXT_ARG: u32 = 1 << 3;

const IORING_SQ_CQ_OVERFLOW: u32 = 1 << 1;

pub const OP_POLL_ADD: u8 = 6;
pub const OP_SENDMSG: u8 = 9;
pub const OP_ACCEPT: u8 = 13;
pub const OP_RECV: u8 = 27;
pub const OP_SEND: u8 = 26;
pub const OP_ASYNC_CANCEL: u8 = 14;

const IOSQE_BUFFER_SELECT: u8 = 1 << 5;
const IORING_RECV_MULTISHOT: u16 = 1 << 1;
const IORING_REGISTER_PBUF_RING: u32 = 22;
const SYS_IO_URING_REGISTER: std::ffi::c_long = 427;
/// The completion names a provided buffer, its id in the high 16 bits.
pub const CQE_F_BUFFER: u32 = 1 << 0;
pub const ENOBUFS: i32 = 105;

const IORING_ACCEPT_MULTISHOT: u16 = 1 << 0;
const IORING_POLL_ADD_MULTI: u32 = 1 << 0;
/// A completion with this flag is not the entry's last.
pub const CQE_F_MORE: u32 = 1 << 1;

pub const POLLIN: u32 = 0x1;
pub const POLLOUT: u32 = 0x4;

const PROT_READ: c_int = 1;
const PROT_WRITE: c_int = 2;
const MAP_SHARED: c_int = 1;
const MAP_POPULATE: c_int = 0x8000;

#[repr(C)]
#[derive(Default)]
struct SqOffsets {
    head: u32,
    tail: u32,
    ring_mask: u32,
    ring_entries: u32,
    flags: u32,
    dropped: u32,
    array: u32,
    resv1: u32,
    user_addr: u64,
}

#[repr(C)]
#[derive(Default)]
struct CqOffsets {
    head: u32,
    tail: u32,
    ring_mask: u32,
    ring_entries: u32,
    overflow: u32,
    cqes: u32,
    flags: u32,
    resv1: u32,
    user_addr: u64,
}

#[repr(C)]
#[derive(Default)]
struct Params {
    sq_entries: u32,
    cq_entries: u32,
    flags: u32,
    sq_thread_cpu: u32,
    sq_thread_idle: u32,
    features: u32,
    wq_fd: u32,
    resv: [u32; 3],
    sq_off: SqOffsets,
    cq_off: CqOffsets,
}

/// `struct io_uring_sqe`, 64 bytes.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Sqe {
    pub opcode: u8,
    pub flags: u8,
    pub ioprio: u16,
    pub fd: i32,
    pub off: u64,
    pub addr: u64,
    pub len: u32,
    /// msg_flags, accept_flags, poll32_events: by opcode.
    pub op_flags: u32,
    pub user_data: u64,
    pub buf_index: u16,
    pub personality: u16,
    pub file_index: i32,
    pub addr3: u64,
    pub pad: u64,
}

const _: () = assert!(std::mem::size_of::<Sqe>() == 64);

/// `struct io_uring_cqe`, 16 bytes.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Cqe {
    pub user_data: u64,
    pub res: i32,
    pub flags: u32,
}

#[repr(C)]
struct GetEventsArg {
    sigmask: u64,
    sigmask_sz: u32,
    min_wait_usec: u32,
    ts: u64,
}

unsafe extern "C" {
    fn syscall(n: std::ffi::c_long, ...) -> std::ffi::c_long;
    fn mmap(addr: *mut u8, len: usize, prot: c_int, flags: c_int, fd: c_int, off: i64) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> c_int;
    fn sysconf(name: c_int) -> std::ffi::c_long;
    fn close(fd: c_int) -> c_int;
}

/// One io_uring, used by one thread.
pub struct Ring {
    fd: c_int,
    sq_ptr: *mut u8,
    sq_len: usize,
    cq_ptr: *mut u8,
    cq_len: usize,
    sqes: *mut Sqe,
    sqes_len: usize,
    sq_head: *const AtomicU32,
    sq_tail: *const AtomicU32,
    sq_flags: *const AtomicU32,
    sq_mask: u32,
    sq_entries: u32,
    sq_array: *mut u32,
    cq_head: *const AtomicU32,
    cq_tail: *const AtomicU32,
    cq_mask: u32,
    cqes: *const Cqe,
    /// Entries written and not yet handed to the kernel.
    local_tail: u32,
    ext_arg: bool,
}

// The ring is used by the thread that made it only (SINGLE_ISSUER).
impl Drop for Ring {
    fn drop(&mut self) {
        unsafe {
            munmap(self.sqes as *mut u8, self.sqes_len);
            if self.cq_ptr != self.sq_ptr {
                munmap(self.cq_ptr, self.cq_len);
            }
            munmap(self.sq_ptr, self.sq_len);
            close(self.fd);
        }
    }
}

impl Ring {
    /// A ring with `entries` submission slots and four times as many
    /// completion slots, with the flags that make a single-threaded
    /// server loop cheapest (single issuer, task work deferred to
    /// `enter`), falling back to fewer flags on older kernels. Err if the
    /// kernel has no io_uring (before 5.1, or disabled by sysctl).
    pub fn new(entries: u32) -> io::Result<Ring> {
        let tries = [
            IORING_SETUP_SINGLE_ISSUER | IORING_SETUP_DEFER_TASKRUN | IORING_SETUP_SUBMIT_ALL,
            IORING_SETUP_COOP_TASKRUN | IORING_SETUP_SUBMIT_ALL,
            0,
        ];
        let mut last = io::Error::from(io::ErrorKind::Unsupported);
        for extra in tries {
            let mut p = Params { flags: IORING_SETUP_CQSIZE | IORING_SETUP_CLAMP | extra, cq_entries: entries * 4, ..Default::default() };
            let fd = unsafe { syscall(SYS_IO_URING_SETUP, entries as std::ffi::c_long, &mut p as *mut Params) } as c_int;
            if fd < 0 {
                last = io::Error::last_os_error();
                if last.raw_os_error() == Some(22) {
                    continue; // EINVAL: a flag this kernel lacks
                }
                return Err(last);
            }
            if p.features & IORING_FEAT_SINGLE_MMAP == 0 || p.features & IORING_FEAT_NODROP == 0 {
                unsafe { close(fd) };
                return Err(io::Error::from(io::ErrorKind::Unsupported));
            }
            return unsafe { Ring::map(fd, &p) };
        }
        Err(last)
    }

    unsafe fn map(fd: c_int, p: &Params) -> io::Result<Ring> {
        unsafe {
            let sq_len = p.sq_off.array as usize + p.sq_entries as usize * 4;
            let cq_len = p.cq_off.cqes as usize + p.cq_entries as usize * std::mem::size_of::<Cqe>();
            let len = sq_len.max(cq_len);
            let ring = mmap(std::ptr::null_mut(), len, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fd, IORING_OFF_SQ_RING);
            if ring as isize == -1 {
                let e = io::Error::last_os_error();
                close(fd);
                return Err(e);
            }
            let sqes_len = p.sq_entries as usize * std::mem::size_of::<Sqe>();
            let sqes = mmap(std::ptr::null_mut(), sqes_len, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fd, IORING_OFF_SQES);
            if sqes as isize == -1 {
                let e = io::Error::last_os_error();
                munmap(ring, len);
                close(fd);
                return Err(e);
            }
            let _ = IORING_OFF_CQ_RING; // one mapping holds both rings (FEAT_SINGLE_MMAP)
            let at = |o: u32| ring.add(o as usize);
            let r = Ring {
                fd,
                sq_ptr: ring,
                sq_len: len,
                cq_ptr: ring,
                cq_len: len,
                sqes: sqes as *mut Sqe,
                sqes_len,
                sq_head: at(p.sq_off.head) as *const AtomicU32,
                sq_tail: at(p.sq_off.tail) as *const AtomicU32,
                sq_flags: at(p.sq_off.flags) as *const AtomicU32,
                sq_mask: *(at(p.sq_off.ring_mask) as *const u32),
                sq_entries: *(at(p.sq_off.ring_entries) as *const u32),
                sq_array: at(p.sq_off.array) as *mut u32,
                cq_head: at(p.cq_off.head) as *const AtomicU32,
                cq_tail: at(p.cq_off.tail) as *const AtomicU32,
                cq_mask: *(at(p.cq_off.ring_mask) as *const u32),
                cqes: at(p.cq_off.cqes) as *const Cqe,
                local_tail: (*(at(p.sq_off.tail) as *const AtomicU32)).load(Ordering::Relaxed),
                ext_arg: p.features & IORING_FEAT_EXT_ARG != 0,
            };
            Ok(r)
        }
    }

    /// Free submission slots.
    fn room(&self) -> u32 {
        let head = unsafe { (*self.sq_head).load(Ordering::Acquire) };
        self.sq_entries - self.local_tail.wrapping_sub(head)
    }

    /// Queues `e`; submits what is queued first if the ring is full.
    pub fn push(&mut self, e: Sqe) {
        if self.room() == 0 {
            let _ = self.enter(0, None);
        }
        let i = self.local_tail & self.sq_mask;
        unsafe {
            *self.sqes.add(i as usize) = e;
            *self.sq_array.add(i as usize) = i;
        }
        self.local_tail = self.local_tail.wrapping_add(1);
    }

    /// Hands queued entries to the kernel and waits for at least
    /// `min_complete` completions, or `timeout_ms` (None: no limit).
    pub fn enter(&mut self, min_complete: u32, timeout_ms: Option<u32>) -> io::Result<()> {
        let tail = unsafe { &*self.sq_tail };
        tail.store(self.local_tail, Ordering::Release);
        let head = unsafe { (*self.sq_head).load(Ordering::Acquire) };
        let to_submit = self.local_tail.wrapping_sub(head);
        let mut flags = 0u32;
        let overflow = unsafe { (*self.sq_flags).load(Ordering::Relaxed) } & IORING_SQ_CQ_OVERFLOW != 0;
        if min_complete > 0 || overflow {
            flags |= IORING_ENTER_GETEVENTS;
        }
        let ts;
        let arg;
        let (argp, argsz) = match timeout_ms {
            Some(ms) if self.ext_arg && min_complete > 0 => {
                ts = crate::sys::timespec { tv_sec: (ms / 1000) as i64, tv_nsec: (ms % 1000) as i64 * 1_000_000 };
                arg = GetEventsArg { sigmask: 0, sigmask_sz: 8, min_wait_usec: 0, ts: &ts as *const crate::sys::timespec as u64 };
                flags |= IORING_ENTER_EXT_ARG;
                (&arg as *const GetEventsArg as *const u8, std::mem::size_of::<GetEventsArg>())
            }
            _ => (std::ptr::null(), 0usize),
        };
        if to_submit == 0 && flags & IORING_ENTER_GETEVENTS == 0 {
            return Ok(());
        }
        loop {
            let r = unsafe { syscall(SYS_IO_URING_ENTER, self.fd as std::ffi::c_long, to_submit as std::ffi::c_long, min_complete as std::ffi::c_long, flags as std::ffi::c_long, argp, argsz) };
            if r >= 0 {
                return Ok(());
            }
            let e = io::Error::last_os_error();
            match e.raw_os_error() {
                Some(4) | Some(62) => return Ok(()), // EINTR, ETIME: the wait ended
                Some(16) => return Ok(()),           // EBUSY: completions to reap first
                _ => return Err(e),
            }
        }
    }

    /// Calls `f` for each completion available now, oldest first.
    #[inline]
    pub fn reap(&mut self, mut f: impl FnMut(Cqe)) -> usize {
        let head_a = unsafe { &*self.cq_head };
        let mut head = head_a.load(Ordering::Relaxed);
        let tail = unsafe { (*self.cq_tail).load(Ordering::Acquire) };
        let n = tail.wrapping_sub(head);
        while head != tail {
            let c = unsafe { *self.cqes.add((head & self.cq_mask) as usize) };
            head = head.wrapping_add(1);
            // Released before `f` runs, so that `f` may submit and enter.
            head_a.store(head, Ordering::Release);
            f(c);
        }
        n as usize
    }
}

/// A ring of receive buffers the kernel picks from (provided buffers,
/// Linux 5.19): a multishot receive takes one per completion and names it
/// in the completion's flags, and the worker gives it back once it has
/// copied the bytes out.
pub struct BufRing {
    ring: *mut u8,
    ring_len: usize,
    mem: Vec<u8>,
    size: usize,
    count: u16,
    tail: u16,
    pub group: u16,
}

#[repr(C)]
struct BufReg {
    ring_addr: u64,
    ring_entries: u32,
    bgid: u16,
    flags: u16,
    resv: [u64; 3],
}

impl BufRing {
    /// `count` (a power of two) buffers of `size` bytes, registered with
    /// `ring` as group `group`, all given to the kernel.
    pub fn new(ring: &Ring, group: u16, count: u16, size: usize) -> io::Result<BufRing> {
        let page = unsafe { sysconf(30) }.max(4096) as usize; // _SC_PAGESIZE
        let ring_len = (count as usize * 16).div_ceil(page) * page;
        const MAP_PRIVATE: c_int = 2;
        const MAP_ANONYMOUS: c_int = 0x20;
        let r = unsafe { mmap(std::ptr::null_mut(), ring_len, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) };
        if r as isize == -1 {
            return Err(io::Error::last_os_error());
        }
        let reg = BufReg { ring_addr: r as u64, ring_entries: count as u32, bgid: group, flags: 0, resv: [0; 3] };
        let rc = unsafe { syscall(SYS_IO_URING_REGISTER, ring.fd as std::ffi::c_long, IORING_REGISTER_PBUF_RING as std::ffi::c_long, &reg as *const BufReg, 1 as std::ffi::c_long) };
        if rc < 0 {
            let e = io::Error::last_os_error();
            unsafe { munmap(r, ring_len) };
            return Err(e);
        }
        let mut b = BufRing { ring: r, ring_len, mem: vec![0u8; count as usize * size], size, count, tail: 0, group };
        for i in 0..count {
            b.put(i);
        }
        b.publish();
        Ok(b)
    }

    /// Buffer `id`'s first `n` bytes.
    #[inline]
    pub fn get(&self, id: u16, n: usize) -> &[u8] {
        let at = (id as usize % self.count as usize) * self.size;
        &self.mem[at..at + n.min(self.size)]
    }

    /// Gives buffer `id` back (seen by the kernel after [`BufRing::publish`]).
    #[inline]
    pub fn put(&mut self, id: u16) {
        let id = id % self.count;
        let slot = (self.tail & (self.count - 1)) as usize;
        let addr = self.mem.as_ptr() as u64 + (id as usize * self.size) as u64;
        unsafe {
            let e = self.ring.add(slot * 16);
            *(e as *mut u64) = addr;
            *(e.add(8) as *mut u32) = self.size as u32;
            *(e.add(12) as *mut u16) = id;
        }
        self.tail = self.tail.wrapping_add(1);
    }

    #[inline]
    pub fn publish(&mut self) {
        // The tail overlays the first entry's last 16 bits.
        let t = unsafe { &*(self.ring.add(14) as *const std::sync::atomic::AtomicU16) };
        t.store(self.tail, Ordering::Release);
    }
}

impl Drop for BufRing {
    fn drop(&mut self) {
        unsafe { munmap(self.ring, self.ring_len) };
    }
}

/// A receive that stays armed (multishot), each completion carrying
/// bytes in a buffer of `group`.
pub fn recv_multishot(fd: i32, group: u16, user_data: u64) -> Sqe {
    Sqe { opcode: OP_RECV, fd, ioprio: IORING_RECV_MULTISHOT, flags: IOSQE_BUFFER_SELECT, buf_index: group, user_data, ..zero() }
}

/// One `send` of `buf[..len]`, which must stay valid until the completion.
pub fn send(fd: i32, buf: *const u8, len: usize, flags: c_int, user_data: u64) -> Sqe {
    Sqe { opcode: OP_SEND, fd, addr: buf as u64, len: len.min(u32::MAX as usize) as u32, op_flags: flags as u32, user_data, ..zero() }
}

/// Cancels the entry submitted with `target` as its user_data.
pub fn cancel(target: u64, user_data: u64) -> Sqe {
    Sqe { opcode: OP_ASYNC_CANCEL, fd: -1, addr: target, user_data, ..zero() }
}

const fn zero() -> Sqe {
    Sqe { opcode: 0, flags: 0, ioprio: 0, fd: 0, off: 0, addr: 0, len: 0, op_flags: 0, user_data: 0, buf_index: 0, personality: 0, file_index: 0, addr3: 0, pad: 0 }
}

/// Accepts connections on `fd` until cancelled, one completion each
/// (nonblocking, close-on-exec), `more` set while it stays armed.
pub fn accept_multishot(fd: i32, user_data: u64) -> Sqe {
    Sqe { opcode: OP_ACCEPT, fd, ioprio: IORING_ACCEPT_MULTISHOT, op_flags: (crate::sys::SOCK_NONBLOCK_FLAG | crate::sys::SOCK_CLOEXEC_FLAG) as u32, user_data, ..zero() }
}

/// One `recv` into `buf[..len]`. The memory must stay valid until the
/// completion arrives.
pub fn recv(fd: i32, buf: *mut u8, len: usize, user_data: u64) -> Sqe {
    Sqe { opcode: OP_RECV, fd, addr: buf as u64, len: len.min(u32::MAX as usize) as u32, user_data, ..zero() }
}

/// One `sendmsg` of `m`. `m`, its `iovec`s and the bytes they name must
/// stay valid until the completion arrives.
pub fn sendmsg(fd: i32, m: *const msghdr, flags: c_int, user_data: u64) -> Sqe {
    Sqe { opcode: OP_SENDMSG, fd, addr: m as u64, len: 1, op_flags: flags as u32, user_data, ..zero() }
}

/// A readiness wait for `events` on `fd`; multishot if `multi`.
pub fn poll(fd: i32, events: u32, multi: bool, user_data: u64) -> Sqe {
    Sqe { opcode: OP_POLL_ADD, fd, len: if multi { IORING_POLL_ADD_MULTI } else { 0 }, op_flags: events, user_data, ..zero() }
}

/// A `msghdr` with up to 8 `iovec`s, kept at a fixed address (boxed) for
/// as long as a `sendmsg` naming it is in flight.
pub struct SendBuf {
    pub m: msghdr,
    pub iov: [iovec; 8],
}

impl SendBuf {
    pub fn new() -> Box<SendBuf> {
        Box::new(SendBuf {
            m: msghdr { msg_name: std::ptr::null_mut(), msg_namelen: 0, msg_iov: std::ptr::null(), msg_iovlen: 0, msg_control: std::ptr::null_mut(), msg_controllen: 0, msg_flags: 0 },
            iov: unsafe { std::mem::zeroed() },
        })
    }

    /// Points the header at `bufs` (at most 8): the bytes they name must
    /// outlive the send.
    pub fn set(&mut self, bufs: &[&[u8]]) -> *const msghdr {
        let k = bufs.len().min(8);
        for (i, b) in bufs[..k].iter().enumerate() {
            self.iov[i] = iovec { iov_base: b.as_ptr(), iov_len: b.len() };
        }
        self.m.msg_iov = self.iov.as_ptr();
        self.m.msg_iovlen = k as _;
        &self.m
    }
}

unsafe extern "C" {
    fn shutdown(fd: c_int, how: c_int) -> c_int;
}

/// `shutdown(fd, SHUT_RDWR)`: in-flight receives and sends on the socket
/// complete at once.
pub fn shutdown_rdwr(fd: i32) {
    unsafe {
        shutdown(fd, 2);
    }
}
