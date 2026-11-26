//! Hints for the encoder: hash lookups into the static and dynamic
//! tables. Nothing here is verified, and nothing needs to be: the encoder
//! checks every hint byte for byte before it uses it, so a wrong hint
//! costs compression, never correctness.

fn static_ids(name: &[u8]) -> &'static [u8] {
    match name {
        b":authority" => &[0],
        b":path" => &[1],
        b"age" => &[2],
        b"content-disposition" => &[3],
        b"content-length" => &[4],
        b"cookie" => &[5],
        b"date" => &[6],
        b"etag" => &[7],
        b"if-modified-since" => &[8],
        b"if-none-match" => &[9],
        b"last-modified" => &[10],
        b"link" => &[11],
        b"location" => &[12],
        b"referer" => &[13],
        b"set-cookie" => &[14],
        b":method" => &[15, 16, 17, 18, 19, 20, 21],
        b":scheme" => &[22, 23],
        b":status" => &[24, 25, 26, 27, 28, 63, 64, 65, 66, 67, 68, 69, 70, 71],
        b"accept" => &[29, 30],
        b"accept-encoding" => &[31],
        b"accept-ranges" => &[32],
        b"access-control-allow-headers" => &[33, 34, 75],
        b"access-control-allow-origin" => &[35],
        b"cache-control" => &[36, 37, 38, 39, 40, 41],
        b"content-encoding" => &[42, 43],
        b"content-type" => &[44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54],
        b"range" => &[55],
        b"strict-transport-security" => &[56, 57, 58],
        b"vary" => &[59, 60],
        b"x-content-type-options" => &[61],
        b"x-xss-protection" => &[62],
        b"accept-language" => &[72],
        b"access-control-allow-credentials" => &[73, 74],
        b"access-control-allow-methods" => &[76, 77, 78],
        b"access-control-expose-headers" => &[79],
        b"access-control-request-headers" => &[80],
        b"access-control-request-method" => &[81, 82],
        b"alt-svc" => &[83],
        b"authorization" => &[84],
        b"content-security-policy" => &[85],
        b"early-data" => &[86],
        b"expect-ct" => &[87],
        b"forwarded" => &[88],
        b"if-range" => &[89],
        b"origin" => &[90],
        b"purpose" => &[91],
        b"server" => &[92],
        b"timing-allow-origin" => &[93],
        b"upgrade-insecure-requests" => &[94],
        b"user-agent" => &[95],
        b"x-forwarded-for" => &[96],
        b"x-frame-options" => &[97, 98],
        _ => &[],
    }
}

/// The static entry with `name: value`, and one with `name`; 99 for none.
#[inline]
pub fn static_find(name: &[u8], value: &[u8]) -> (usize, usize) {
    let ids = static_ids(name);
    if ids.is_empty() {
        return (99, 99);
    }
    for &i in ids {
        if crate::stable::STATIC[i as usize].1 == value {
            return (i as usize, i as usize);
        }
    }
    (99, ids[0] as usize)
}

#[inline]
fn mix(h: u64, w: u64) -> u64 {
    (h ^ w).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29)
}

/// A hash of a field.
#[inline]
pub fn hash(name: &[u8], value: &[u8]) -> u64 {
    let mut h = (name.len() as u64) << 32 | value.len() as u64;
    for s in [name, value] {
        let mut c = s.chunks_exact(8);
        for w in &mut c {
            h = mix(h, u64::from_le_bytes(w.try_into().unwrap()));
        }
        let r = c.remainder();
        let mut t = 0u64;
        for (k, &b) in r.iter().enumerate() {
            t |= (b as u64) << (8 * k);
        }
        h = mix(h, t ^ 0xff);
    }
    h | 1
}

const SEEN: usize = 512;

/// Where the dynamic table may hold a field, by hash: one slot a hash,
/// newer entries overwriting older ones. A lost or stale slot costs a
/// missed reference, nothing more.
pub struct Index {
    slots: Vec<(u64, u64)>,
    mask: usize,
    seen: Vec<u64>,
}

impl Index {
    pub fn new(cap: u64) -> Index {
        let n = ((cap / 32) as usize * 4).next_power_of_two().max(64);
        Index { slots: vec![(0, 0); n], mask: n - 1, seen: vec![0; SEEN] }
    }

    #[inline]
    pub fn find(&self, h: u64) -> Option<u64> {
        let s = self.slots[(h >> 20) as usize & self.mask];
        if s.0 == h { Some(s.1) } else { None }
    }

    /// True the second time a field is seen (in a window of recent
    /// fields): a field seen once is often seen again.
    #[inline]
    pub fn worth(&mut self, h: u64) -> bool {
        let slot = (h >> 40) as usize % SEEN;
        if self.seen[slot] == h {
            true
        } else {
            self.seen[slot] = h;
            false
        }
    }

    #[inline]
    pub fn add(&mut self, h: u64, a: u64) {
        self.slots[(h >> 20) as usize & self.mask] = (h, a);
    }
}
