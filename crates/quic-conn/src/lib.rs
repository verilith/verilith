//! A sans-I/O QUIC version 1 server (RFC 9000, 9001, 9002) built from
//! Verilith's verified pieces: `verilith-quic` (wire format, flow control,
//! stream states, loss recovery, congestion control) and `verilith-tls`
//! (the TLS 1.3 handshake for QUIC, packet and header protection).
//!
//! [`Server`] routes datagrams to [`Connection`]s by connection ID and
//! answers unknown versions; the caller owns the socket and the clock (in
//! microseconds, from any epoch).
pub mod buf;
pub mod conn;

pub use conn::{Config, Connection, Event, StreamError, Transmit, CID_LEN};

use std::collections::HashMap;
use std::sync::Arc;
use verilith_quic::packet::{self, Header};
use verilith_tls::crypto::Provider;

/// What a datagram did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Datagram {
    /// It was for this connection (new or existing).
    Conn(usize),
    /// A stateless response is in the buffer (Version Negotiation).
    Response(usize),
    /// Discarded.
    Dropped,
}

/// Connections on one socket.
pub struct Server<P: Provider> {
    cfg: Arc<Config<P>>,
    prov: P,
    conns: Vec<Option<Connection<P>>>,
    free: Vec<usize>,
    /// Client-chosen Destination Connection IDs of connections still in
    /// their handshake.
    initial: HashMap<Vec<u8>, usize>,
}

impl<P: Provider> Server<P> {
    pub fn new(cfg: Arc<Config<P>>) -> Server<P> {
        let prov = (cfg.provider)();
        Server { cfg, prov, conns: Vec::new(), free: Vec::new(), initial: HashMap::new() }
    }

    /// The connection in slot `i`.
    pub fn conn(&mut self, i: usize) -> Option<&mut Connection<P>> {
        self.conns.get_mut(i).and_then(|c| c.as_mut())
    }

    /// Slots in use.
    pub fn len(&self) -> usize {
        self.conns.len()
    }

    /// Removes connection `i` if it is closed; true if it was.
    pub fn reap(&mut self, i: usize) -> bool {
        let closed = matches!(self.conns.get(i), Some(Some(c)) if c.is_closed());
        if closed {
            let c = self.conns[i].take().unwrap();
            self.initial.remove(&c.odcid);
            self.free.push(i);
        }
        closed
    }

    /// Handles a datagram from the network. A stateless response, if any,
    /// is written to `out`.
    pub fn handle(&mut self, now: u64, data: &mut [u8], out: &mut Vec<u8>) -> Datagram {
        let Some((h, _)) = packet::parse_header(data, 0, CID_LEN) else { return Datagram::Dropped };
        let slot = match h {
            Header::Short { dcid, .. } => self.slot_of(dcid),
            Header::Long { first, dcid, scid, .. } => {
                if let Some(i) = self.slot_of(dcid) {
                    Some(i)
                } else if let Some(&i) = self.initial.get(dcid) {
                    Some(i)
                } else if (first >> 4) & 3 == 0 {
                    // A new connection: the Initial must fill a datagram of
                    // 1200 bytes (§14.1).
                    if data.len() < 1200 || dcid.len() < 8 {
                        return Datagram::Dropped;
                    }
                    let i = match self.free.pop() {
                        Some(i) => i,
                        None => {
                            self.conns.push(None);
                            self.conns.len() - 1
                        }
                    };
                    let mut rnd = [0u8; 32];
                    self.prov.random(&mut rnd);
                    let mut cid = [0u8; CID_LEN];
                    cid[..4].copy_from_slice(&(i as u32).to_be_bytes());
                    cid[4..].copy_from_slice(&rnd[..CID_LEN - 4]);
                    let Some(c) = Connection::new(self.cfg.clone(), now, dcid, scid, cid) else {
                        self.free.push(i);
                        return Datagram::Dropped;
                    };
                    self.initial.insert(dcid.to_vec(), i);
                    self.conns[i] = Some(c);
                    Some(i)
                } else {
                    None
                }
            }
            Header::OtherVersion { dcid, scid, .. } => {
                // Version Negotiation (§6, §17.2.1), for datagrams big
                // enough to be a client's first.
                if data.len() < 1200 {
                    return Datagram::Dropped;
                }
                out.clear();
                let mut r = [0u8; 32];
                self.prov.random(&mut r);
                out.push(0x80 | (r[0] & 0x7f));
                out.extend_from_slice(&0u32.to_be_bytes());
                out.push(scid.len() as u8);
                out.extend_from_slice(scid);
                out.push(dcid.len() as u8);
                out.extend_from_slice(dcid);
                out.extend_from_slice(&1u32.to_be_bytes());
                return Datagram::Response(out.len());
            }
            _ => None,
        };
        let Some(i) = slot else { return Datagram::Dropped };
        let Some(Some(c)) = self.conns.get_mut(i) else { return Datagram::Dropped };
        c.handle_datagram(now, data);
        if !c.is_handshaking() {
            let k = c.odcid.clone();
            self.initial.remove(&k);
        }
        Datagram::Conn(i)
    }

    fn slot_of(&self, dcid: &[u8]) -> Option<usize> {
        if dcid.len() != CID_LEN {
            return None;
        }
        let i = u32::from_be_bytes([dcid[0], dcid[1], dcid[2], dcid[3]]) as usize;
        match self.conns.get(i) {
            Some(Some(c)) if c.local_cid[..] == *dcid => Some(i),
            _ => None,
        }
    }
}
