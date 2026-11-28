//! The transport to authoritative servers (unverified glue; TRUST.md):
//! UDP from a fresh socket with an OS-chosen port per query, connected to
//! the server so the kernel drops datagrams from any other address or
//! port, then TCP when a response is truncated.
use std::hash::{BuildHasher, Hasher};
use std::io::{Read, Write};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, TcpStream, UdpSocket};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use crate::resolve::Transport;

/// The IPv4 addresses of the root servers (a to m.root-servers.net, IANA
/// root hints).
pub const ROOTS_V4: [[u8; 4]; 13] = [
    [198, 41, 0, 4],
    [170, 247, 170, 2],
    [192, 33, 4, 12],
    [199, 7, 91, 13],
    [192, 203, 230, 10],
    [192, 5, 5, 241],
    [192, 112, 36, 4],
    [198, 97, 190, 53],
    [192, 36, 148, 17],
    [192, 58, 128, 30],
    [193, 0, 14, 129],
    [199, 7, 83, 42],
    [202, 12, 27, 33],
];

pub struct Upstream {
    /// The port servers are asked on: 53, or another for a test hierarchy.
    pub port: u16,
    /// How long to wait for one server before trying the next.
    pub timeout: Duration,
    start: Instant,
    keys: std::collections::hash_map::RandomState,
    counter: AtomicU64,
}

impl Upstream {
    pub fn new(port: u16, timeout: Duration) -> Upstream {
        Upstream { port, timeout, start: Instant::now(), keys: Default::default(), counter: AtomicU64::new(0) }
    }

    fn addr(&self, a: &[u8]) -> Option<SocketAddr> {
        let ip = match a.len() {
            4 => IpAddr::V4(Ipv4Addr::new(a[0], a[1], a[2], a[3])),
            16 => {
                let mut b = [0u8; 16];
                b.copy_from_slice(a);
                IpAddr::V6(Ipv6Addr::from(b))
            }
            _ => return None,
        };
        Some(SocketAddr::new(ip, self.port))
    }

    fn udp(&self, to: SocketAddr, query: &[u8]) -> Option<Vec<u8>> {
        let local: SocketAddr = if to.is_ipv4() { "0.0.0.0:0".parse().unwrap() } else { "[::]:0".parse().unwrap() };
        let s = UdpSocket::bind(local).ok()?;
        s.connect(to).ok()?;
        s.send(query).ok()?;
        let deadline = Instant::now() + self.timeout;
        let mut buf = vec![0u8; 65535];
        loop {
            let left = deadline.checked_duration_since(Instant::now())?;
            if left.is_zero() {
                return None;
            }
            s.set_read_timeout(Some(left)).ok()?;
            let n = s.recv(&mut buf).ok()?;
            // Skip datagrams with another ID; the verified check
            // (`response_ok`) decides about the rest.
            if n >= 12 && buf[..2] == query[..2] {
                buf.truncate(n);
                return Some(buf);
            }
        }
    }

    fn tcp(&self, to: SocketAddr, query: &[u8]) -> Option<Vec<u8>> {
        let mut s = TcpStream::connect_timeout(&to, self.timeout).ok()?;
        s.set_read_timeout(Some(self.timeout)).ok()?;
        s.set_write_timeout(Some(self.timeout)).ok()?;
        let _ = s.set_nodelay(true);
        let mut out = Vec::with_capacity(query.len() + 2);
        out.extend_from_slice(&(query.len() as u16).to_be_bytes());
        out.extend_from_slice(query);
        s.write_all(&out).ok()?;
        let mut len = [0u8; 2];
        s.read_exact(&mut len).ok()?;
        let mut buf = vec![0u8; u16::from_be_bytes(len) as usize];
        s.read_exact(&mut buf).ok()?;
        Some(buf)
    }
}

impl Transport for Upstream {
    fn exchange(&self, addr: &[u8], query: &[u8]) -> Option<Vec<u8>> {
        if query.len() < 12 || query.len() > 65535 {
            return None;
        }
        let to = self.addr(addr)?;
        let r = self.udp(to, query)?;
        // TC: ask again over TCP (RFC 7766 §5).
        if r[2] & 0x02 != 0 { self.tcp(to, query) } else { Some(r) }
    }

    fn now(&self) -> u64 {
        self.start.elapsed().as_secs() + 1
    }

    /// SipHash, keyed from the OS's randomness when the process started,
    /// of a counter: unpredictable to anyone who cannot read the key.
    fn random(&self) -> u64 {
        let mut h = self.keys.build_hasher();
        h.write_u64(self.counter.fetch_add(1, Ordering::Relaxed));
        h.finish()
    }
}
