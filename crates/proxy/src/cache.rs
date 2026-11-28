//! The shared response cache: what to store and for how long is decided
//! by the verified rules (`rules.rs`); this file only keeps the entries.
//!
//! Plain Rust, trusted (TRUST.md). One cache for all workers, split into
//! shards behind their own locks; entries are evicted oldest first once
//! the cache holds more than its byte budget. A stored body is the
//! backend's, uncompressed; the compressed forms the proxy sends are made
//! once per coding and kept with the entry.
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::coding::Coding;

const SHARDS: usize = 32;

pub struct Entry {
    pub status: u16,
    /// The response's fields, already filtered for the client (no
    /// hop-by-hop fields, no Date, Server or Age).
    pub fields: Vec<(Vec<u8>, Vec<u8>)>,
    pub body: Arc<[u8]>,
    pub stored: Instant,
    /// Freshness lifetime and the backend's Age when stored (seconds).
    pub lifetime: u64,
    pub age: u64,
    /// Whether the proxy may compress the body, and the compressed forms
    /// made so far (Brotli, Zstandard, gzip).
    pub compressible: bool,
    pub variants: Mutex<[Option<Arc<[u8]>>; 3]>,
}

impl Entry {
    pub fn size(&self) -> usize {
        self.body.len() + self.fields.iter().map(|(n, v)| n.len() + v.len() + 16).sum::<usize>() + 256
    }

    pub fn variant(&self, c: Coding) -> Option<Arc<[u8]>> {
        self.variants.lock().unwrap_or_else(|e| e.into_inner())[slot(c)].clone()
    }

    pub fn set_variant(&self, c: Coding, b: Arc<[u8]>) {
        self.variants.lock().unwrap_or_else(|e| e.into_inner())[slot(c)] = Some(b);
    }
}

fn slot(c: Coding) -> usize {
    match c {
        Coding::Br => 0,
        Coding::Zstd => 1,
        Coding::Gzip => 2,
    }
}

struct Shard {
    map: HashMap<Vec<u8>, Arc<Entry>>,
    order: VecDeque<Vec<u8>>,
    bytes: usize,
}

pub struct Cache {
    shards: Vec<Mutex<Shard>>,
    /// Byte budget per shard, and the largest entry stored.
    shard_max: usize,
    pub max_entry: usize,
}

impl Cache {
    pub fn new(max_bytes: usize, max_entry: usize) -> Cache {
        Cache {
            shards: (0..SHARDS).map(|_| Mutex::new(Shard { map: HashMap::new(), order: VecDeque::new(), bytes: 0 })).collect(),
            shard_max: (max_bytes / SHARDS).max(1),
            max_entry,
        }
    }

    fn shard(&self, key: &[u8]) -> &Mutex<Shard> {
        // FNV-1a: keys are host and target, chosen by clients.
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for &b in key {
            h = (h ^ b as u64).wrapping_mul(0x100_0000_01b3);
        }
        &self.shards[(h % SHARDS as u64) as usize]
    }

    pub fn get(&self, key: &[u8]) -> Option<Arc<Entry>> {
        self.shard(key).lock().unwrap_or_else(|e| e.into_inner()).map.get(key).cloned()
    }

    pub fn remove(&self, key: &[u8]) {
        let mut s = self.shard(key).lock().unwrap_or_else(|e| e.into_inner());
        if let Some(e) = s.map.remove(key) {
            s.bytes -= e.size();
        }
    }

    pub fn put(&self, key: Vec<u8>, e: Entry) {
        let size = e.size();
        if size > self.max_entry || size > self.shard_max {
            return;
        }
        let mut s = self.shard(&key).lock().unwrap_or_else(|e| e.into_inner());
        if let Some(old) = s.map.insert(key.clone(), Arc::new(e)) {
            s.bytes -= old.size();
        } else {
            s.order.push_back(key);
        }
        s.bytes += size;
        while s.bytes > self.shard_max {
            let Some(k) = s.order.pop_front() else { break };
            if let Some(old) = s.map.remove(&k) {
                s.bytes -= old.size();
            }
        }
        // Keys removed by `remove` linger in `order` until they reach the
        // front; keep the queue from growing without bound.
        if s.order.len() > 2 * s.map.len() + 64 {
            let Shard { map, order, .. } = &mut *s;
            order.retain(|k| map.contains_key(k));
        }
    }
}
