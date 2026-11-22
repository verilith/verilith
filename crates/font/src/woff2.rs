//! Reading WOFF2: the table directory, the Brotli stream (decoded by
//! vbrotli), and undoing the `glyf`/`loca` and `hmtx` transforms.
//!
//! Like `build`, this module is verified for memory safety and absence of
//! overflow only. What it reconstructs goes through the same rebuilding
//! and the same final verified check as any other input.
use crate::build::*;
use crate::prims::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// A cursor over a byte slice.
pub struct Rd<'a> {
    pub s: &'a [u8],
    pub p: usize,
}

impl<'a> Rd<'a> {
    pub open spec fn ok(&self) -> bool {
        self.p <= self.s@.len()
    }

    pub fn new(s: &'a [u8]) -> (r: Rd<'a>)
        ensures
            r.ok(),
            r.s == s,
    {
        Rd { s, p: 0 }
    }

    pub fn left(&self) -> (n: usize)
        requires
            self.ok(),
        ensures
            n == self.s@.len() - self.p,
    {
        self.s.len() - self.p
    }

    pub fn u8(&mut self) -> (r: Option<u8>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).s == old(self).s,
            final(self).p >= old(self).p,
            r is Some ==> final(self).p == old(self).p + 1,
    {
        if self.s.len() - self.p < 1 {
            return None;
        }
        let v = rd8(self.s, self.p);
        self.p = self.p + 1;
        Some(v)
    }

    pub fn u16(&mut self) -> (r: Option<u16>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).s == old(self).s,
            final(self).p >= old(self).p,
    {
        if self.s.len() - self.p < 2 {
            return None;
        }
        let v = rd16(self.s, self.p);
        self.p = self.p + 2;
        Some(v)
    }

    pub fn u32(&mut self) -> (r: Option<u32>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).s == old(self).s,
            final(self).p >= old(self).p,
    {
        if self.s.len() - self.p < 4 {
            return None;
        }
        let v = rd32(self.s, self.p);
        self.p = self.p + 4;
        Some(v)
    }

    /// The next `n` bytes.
    pub fn take(&mut self, n: usize) -> (r: Option<&'a [u8]>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).s == old(self).s,
            final(self).p >= old(self).p,
            r matches Some(x) ==> x@.len() == n && final(self).p == old(self).p + n,
    {
        if self.s.len() - self.p < n {
            return None;
        }
        let x = slice(self.s, self.p, self.p + n);
        self.p = self.p + n;
        Some(x)
    }

    /// A 255UInt16.
    pub fn u255(&mut self) -> (r: Option<u32>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).s == old(self).s,
            final(self).p >= old(self).p,
            r is Some ==> final(self).p > old(self).p,
            r matches Some(v) ==> v <= 65535,
    {
        let c = self.u8()?;
        if c == 253 {
            Some(self.u16()? as u32)
        } else if c == 255 {
            Some(self.u8()? as u32 + 253)
        } else if c == 254 {
            Some(self.u8()? as u32 + 506)
        } else {
            Some(c as u32)
        }
    }

    /// A UIntBase128.
    pub fn base128(&mut self) -> (r: Option<u32>)
        requires
            old(self).ok(),
        ensures
            final(self).ok(),
            final(self).s == old(self).s,
            final(self).p >= old(self).p,
    {
        let mut acc: u32 = 0;
        let mut i: usize = 0;
        while i < 5
            invariant
                i <= 5,
                self.ok(),
                self.s == old(self).s,
                self.p >= old(self).p,
            decreases 5 - i,
        {
            let b = self.u8()?;
            // No leading zeros, and no overflow past 32 bits.
            if (i == 0 && b == 0x80) || acc >= 0x0200_0000 {
                return None;
            }
            acc = acc * 128 + (b % 128) as u32;
            if b < 128 {
                return Some(acc);
            }
            i += 1;
        }
        None
    }
}

/// The tag for a WOFF2 known-table index (0 to 62).
fn known_tag_at(i: usize) -> (r: u32)
    requires
        i < 63,
{
    let tags: [u32; 63] = [
        0x636d6170, 0x68656164, 0x68686561, 0x686d7478, 0x6d617870, 0x6e616d65, 0x4f532f32,
        0x706f7374, 0x63767420, 0x6670676d, 0x676c7966, 0x6c6f6361, 0x70726570, 0x43464620,
        0x564f5247, 0x45424454, 0x45424c43, 0x67617370, 0x68646d78, 0x6b65726e, 0x4c545348,
        0x50434c54, 0x56444d58, 0x76686561, 0x766d7478, 0x42415345, 0x47444546, 0x47504f53,
        0x47535542, 0x45425343, 0x4a535446, 0x4d415448, 0x43424454, 0x43424c43, 0x434f4c52,
        0x4350414c, 0x53564720, 0x73626978, 0x61636e74, 0x61766172, 0x62646174, 0x626c6f63,
        0x62736c6e, 0x63766172, 0x66647363, 0x66656174, 0x666d7478, 0x66766172, 0x67766172,
        0x68737479, 0x6a757374, 0x6c636172, 0x6d6f7274, 0x6d6f7278, 0x6f706264, 0x70726f70,
        0x7472616b, 0x5a617066, 0x53696c66, 0x476c6174, 0x476c6f63, 0x46656174, 0x53696c6c,
    ];
    tags[i]
}

/// One entry of the WOFF2 table directory.
pub struct Entry {
    pub tag: u32,
    /// The table is stored transformed.
    pub xform: bool,
    /// Where its bytes start in the decompressed stream, and how many.
    pub off: usize,
    pub len: usize,
}

pub const T_GLYF_: u32 = 0x676C_7966;

/// `n` zero bytes.
fn zeros_vec(n: usize) -> (v: Vec<u8>)
    ensures
        v@.len() == n,
{
    let mut v: Vec<u8> = Vec::new();
    v.resize(n, 0u8);
    v
}

/// Decompresses a whole Brotli stream that must produce exactly `n` bytes.
fn brotli_exact(src: &[u8], n: usize) -> (r: Option<Vec<u8>>)
    requires
        src.len() <= u32::MAX,
    ensures
        r matches Some(v) ==> v@.len() == n,
{
    let mut out = zeros_vec(n);
    let mut s = verilith_brotli::stream::Stream::new(Ghost(src@));
    proof {
        assert(src@.subrange(0, src@.len() as int) =~= src@);
    }
    let (r, _used, made) = s.decompress(src, out.as_mut_slice());
    match r {
        verilith_brotli::stream::Result::Success => {
            if made == n {
                Some(out)
            } else {
                None
            }
        },
        _ => None,
    }
}

fn put_i16(v: &mut Vec<u8>, x: i64)
    requires
        -32768 <= x <= 32767,
    ensures
        final(v)@.len() == old(v)@.len() + 2,
{
    let u = if x < 0 {
        x + 65536
    } else {
        x
    };
    put16(v, u as u16);
}

/// `v` or its negation.
fn sgn(pos: bool, v: i64) -> (r: i64)
    requires
        0 <= v < 65536,
    ensures
        -65536 < r < 65536,
{
    if pos {
        v
    } else {
        -v
    }
}

/// The (dx, dy, on-curve) a WOFF2 point triplet encodes: flag byte `f`
/// and its data from `g`.
fn triplet(f: u8, g: &mut Rd) -> (r: Option<(i64, i64, bool)>)
    requires
        old(g).ok(),
    ensures
        final(g).ok(),
        final(g).s == old(g).s,
        r matches Some((dx, dy, _)) ==> -65536 < dx < 65536 && -65536 < dy < 65536,
{
    let on = f < 128;
    let b = (f % 128) as i64;
    let sx = b % 2 == 1;
    let sy = (b / 2) % 2 == 1;
    if b < 10 {
        let v = ((b / 2) % 8) * 256 + g.u8()? as i64;
        Some((0, sgn(sx, v), on))
    } else if b < 20 {
        let v = (((b - 10) / 2) % 8) * 256 + g.u8()? as i64;
        Some((sgn(sx, v), 0, on))
    } else if b < 84 {
        let b0 = b - 20;
        let b1 = g.u8()? as i64;
        let dx = 1 + (b0 / 16) % 4 * 16 + b1 / 16;
        let dy = 1 + (b0 / 4) % 4 * 16 + b1 % 16;
        Some((sgn(sx, dx), sgn(sy, dy), on))
    } else if b < 120 {
        let b0 = b - 84;
        let x = g.u8()? as i64;
        let y = g.u8()? as i64;
        let dx = 1 + (b0 / 12) * 256 + x;
        let dy = 1 + ((b0 % 12) / 4) * 256 + y;
        Some((sgn(sx, dx), sgn(sy, dy), on))
    } else if b < 124 {
        let x0 = g.u8()? as i64;
        let b2 = g.u8()? as i64;
        let y1 = g.u8()? as i64;
        let dx = x0 * 16 + b2 / 16;
        let dy = (b2 % 16) * 256 + y1;
        Some((sgn(sx, dx), sgn(sy, dy), on))
    } else {
        let dx = g.u16()? as i64;
        let dy = g.u16()? as i64;
        Some((sgn(sx, dx), sgn(sy, dy), on))
    }
}

/// Appends one coordinate delta to `out` in `glyf` form and returns the
/// flag bits for it: `short` and `same` are that axis's two flag bits.
fn put_coord(out: &mut Vec<u8>, d: i64, short: u8, same: u8) -> (r: Option<u8>)
    requires
        -65536 < d < 65536,
        short as int + same as int <= 0x30,
    ensures
        r matches Some(f) ==> f <= short + same,
{
    if d == 0 {
        Some(same)
    } else if -256 < d && d < 256 {
        if d > 0 {
            out.push(d as u8);
            Some(short + same)
        } else {
            out.push((-d) as u8);
            Some(short)
        }
    } else {
        if d < -32768 || d > 32767 {
            return None;
        }
        put_i16(out, d);
        Some(0)
    }
}

/// Coordinates beyond this are refused.
const COORD_LIMIT: i64 = 0x4000_0000;

/// The seven streams of a transformed `glyf` table.
struct Streams<'a> {
    ncont: Rd<'a>,
    npts: Rd<'a>,
    flag: Rd<'a>,
    glyph: Rd<'a>,
    comp: Rd<'a>,
    bbox: Rd<'a>,
    instr: Rd<'a>,
}

impl<'a> Streams<'a> {
    spec fn ok(&self) -> bool {
        &&& self.ncont.ok()
        &&& self.npts.ok()
        &&& self.flag.ok()
        &&& self.glyph.ok()
        &&& self.comp.ok()
        &&& self.bbox.ok()
        &&& self.instr.ok()
    }
}

/// Rebuilds one simple glyph of `nc` contours onto `out`. `bbox` is its
/// explicit bounding box, if it has one. Returns its xMin.
fn simple_glyph(st: &mut Streams, nc: usize, bbox: Option<&[u8]>, overlap: bool, out: &mut Vec<u8>) -> (r:
    Option<i64>)
    requires
        old(st).ok(),
        1 <= nc <= 32767,
        bbox matches Some(b) ==> b@.len() == 8,
    ensures
        final(st).ok(),
{
    // End points.
    let mut ends: Vec<u8> = Vec::new();
    let mut total: usize = 0;
    let mut k: usize = 0;
    while k < nc
        invariant
            k <= nc,
            st.ok(),
            total <= 65536,
        decreases nc - k,
    {
        let n = st.npts.u255()? as usize;
        total = total + n;
        if total == 0 || total > 65536 {
            return None;
        }
        put16(&mut ends, (total - 1) as u16);
        k += 1;
    }
    // Points.
    let mut flags: Vec<u8> = Vec::new();
    let mut xs: Vec<u8> = Vec::new();
    let mut ys: Vec<u8> = Vec::new();
    let mut x: i64 = 0;
    let mut y: i64 = 0;
    let mut xmin: i64 = 0;
    let mut xmax: i64 = 0;
    let mut ymin: i64 = 0;
    let mut ymax: i64 = 0;
    let mut last: u8 = 0;
    let mut rep: u8 = 0;
    let mut i: usize = 0;
    while i < total
        invariant
            i <= total,
            st.ok(),
            -COORD_LIMIT <= x <= COORD_LIMIT,
            -COORD_LIMIT <= y <= COORD_LIMIT,
            -COORD_LIMIT <= xmin <= xmax <= COORD_LIMIT,
            -COORD_LIMIT <= ymin <= ymax <= COORD_LIMIT,
            i > 0 ==> flags@.len() > 0,
            rep > 0 ==> i > 0,
        decreases total - i,
    {
        let f = st.flag.u8()?;
        let (dx, dy, on) = triplet(f, &mut st.glyph)?;
        x = x + dx;
        y = y + dy;
        if x < -COORD_LIMIT || x > COORD_LIMIT || y < -COORD_LIMIT || y > COORD_LIMIT {
            return None;
        }
        if i == 0 {
            xmin = x;
            xmax = x;
            ymin = y;
            ymax = y;
        } else {
            if x < xmin {
                xmin = x;
            }
            if x > xmax {
                xmax = x;
            }
            if y < ymin {
                ymin = y;
            }
            if y > ymax {
                ymax = y;
            }
        }
        let fx = put_coord(&mut xs, dx, 0x02, 0x10)?;
        let fy = put_coord(&mut ys, dy, 0x04, 0x20)?;
        let mut fl: u8 = fx + fy;
        if on {
            fl = fl + 1;
        }
        if i == 0 && overlap {
            fl = fl + 0x40;
        }
        if i > 0 && fl == last && rep < 255 {
            rep = rep + 1;
        } else {
            if rep > 0 {
                // Turn the previous flag into a repeated one.
                let j = flags.len() - 1;
                let prev = flags[j];
                flags.set(j, if prev % 16 >= 8 {
                    prev
                } else {
                    (prev % 128) + 8
                });
                flags.push(rep);
            }
            flags.push(fl);
            rep = 0;
        }
        last = fl;
        i += 1;
    }
    if rep > 0 && flags.len() > 0 {
        let j = flags.len() - 1;
        let prev = flags[j];
        flags.set(j, if prev % 16 >= 8 {
            prev
        } else {
            (prev % 128) + 8
        });
        flags.push(rep);
    }
    let ilen = st.glyph.u255()? as usize;
    let ins = st.instr.take(ilen)?;
    put16(out, nc as u16);
    let x_min = match bbox {
        Some(b) => {
            append(out, b);
            rdi16(b, 0) as i64
        },
        None => {
            if xmin < -32768 || xmax > 32767 || ymin < -32768 || ymax > 32767 {
                return None;
            }
            put_i16(out, xmin);
            put_i16(out, ymin);
            put_i16(out, xmax);
            put_i16(out, ymax);
            xmin
        },
    };
    append(out, ends.as_slice());
    put16(out, ilen as u16);
    append(out, ins);
    append(out, flags.as_slice());
    append(out, xs.as_slice());
    append(out, ys.as_slice());
    Some(x_min)
}

/// Rebuilds one composite glyph onto `out`. Returns its xMin.
fn composite_glyph(st: &mut Streams, bbox: &[u8], out: &mut Vec<u8>) -> (r: Option<i64>)
    requires
        old(st).ok(),
        bbox@.len() == 8,
    ensures
        final(st).ok(),
{
    put16(out, 0xFFFF);
    append(out, bbox);
    let mut have_instr = false;
    loop
        invariant
            st.ok(),
        decreases st.comp.s@.len() - st.comp.p,
    {
        let fl = st.comp.take(2)?;
        let hi = rd8(fl, 0);
        let lo = rd8(fl, 1);
        let mut n: usize = 2;
        n = n + (if lo % 2 == 1 {
            4usize
        } else {
            2
        });
        n = n + (if (lo / 8) % 2 == 1 {
            2usize
        } else if (lo / 64) % 2 == 1 {
            4
        } else if lo >= 128 {
            8
        } else {
            0
        });
        let rest = st.comp.take(n)?;
        append(out, fl);
        append(out, rest);
        if hi % 2 == 1 {
            have_instr = true;
        }
        if (lo / 32) % 2 == 0 {
            break ;
        }
    }
    if have_instr {
        let ilen = st.glyph.u255()? as usize;
        let ins = st.instr.take(ilen)?;
        put16(out, ilen as u16);
        append(out, ins);
    }
    Some(rdi16(bbox, 0) as i64)
}

/// Undoes the WOFF2 `glyf` transform. Returns `glyf`, a long-format
/// `loca`, the number of glyphs, and each glyph's xMin (for `hmtx`).
pub fn untransform_glyf(t: &[u8]) -> (r: Option<(Vec<u8>, Vec<u8>, u16, Vec<i64>)>)
    ensures
        r matches Some((_, _, ng, xm)) ==> xm@.len() == ng,
{
    let mut h = Rd::new(t);
    let _version = h.u16()?;
    let opts = h.u16()?;
    let ng = h.u16()?;
    let _index_format = h.u16()?;
    let n1 = h.u32()? as usize;
    let n2 = h.u32()? as usize;
    let n3 = h.u32()? as usize;
    let n4 = h.u32()? as usize;
    let n5 = h.u32()? as usize;
    let n6 = h.u32()? as usize;
    let n7 = h.u32()? as usize;
    let ncont = Rd::new(h.take(n1)?);
    let npts = Rd::new(h.take(n2)?);
    let flag = Rd::new(h.take(n3)?);
    let glyph = Rd::new(h.take(n4)?);
    let comp = Rd::new(h.take(n5)?);
    let bbox_all = h.take(n6)?;
    let instr = Rd::new(h.take(n7)?);
    let n = ng as usize;
    let overlap_map: Option<&[u8]> = if opts % 2 == 1 {
        Some(h.take((n + 7) / 8)?)
    } else {
        None
    };
    let mut bb = Rd::new(bbox_all);
    let bitmap = bb.take(4 * ((n + 31) / 32))?;
    let mut st = Streams { ncont, npts, flag, glyph, comp, bbox: bb, instr };
    let mut out: Vec<u8> = Vec::new();
    let mut loca: Vec<u8> = Vec::new();
    let mut xmins: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == ng,
            st.ok(),
            xmins@.len() == i,
            bitmap@.len() == 4 * ((n + 31) / 32),
            overlap_map matches Some(m) ==> m@.len() == (n + 7) / 8,
        decreases n - i,
    {
        if out.len() > u32::MAX as usize {
            return None;
        }
        put32(&mut loca, out.len() as u32);
        let nc = rd16(st.ncont.take(2)?, 0);
        let has_bbox = (rd8(bitmap, i / 8) / pow2_u8(7 - (i % 8))) % 2 == 1;
        let overlap = match overlap_map {
            Some(m) => (rd8(m, i / 8) / pow2_u8(7 - (i % 8))) % 2 == 1,
            None => false,
        };
        let xmin = if nc == 0 {
            if has_bbox {
                return None;
            }
            0
        } else if nc == 0xFFFF {
            if !has_bbox {
                return None;
            }
            let b = st.bbox.take(8)?;
            composite_glyph(&mut st, b, &mut out)?
        } else if nc < 0x8000 {
            let b = if has_bbox {
                Some(st.bbox.take(8)?)
            } else {
                None
            };
            simple_glyph(&mut st, nc as usize, b, overlap, &mut out)?
        } else {
            return None;
        };
        pad(&mut out);
        xmins.push(xmin);
        i += 1;
    }
    if out.len() > u32::MAX as usize {
        return None;
    }
    put32(&mut loca, out.len() as u32);
    Some((out, loca, ng, xmins))
}

/// 2 to the power `k`.
fn pow2_u8(k: usize) -> (r: u8)
    requires
        k <= 7,
    ensures
        r >= 1,
{
    if k == 0 {
        1
    } else if k == 1 {
        2
    } else if k == 2 {
        4
    } else if k == 3 {
        8
    } else if k == 4 {
        16
    } else if k == 5 {
        32
    } else if k == 6 {
        64
    } else {
        128
    }
}

/// Undoes the WOFF2 `hmtx` transform: left side bearings that were left
/// out are the glyphs' xMin.
pub fn untransform_hmtx(t: &[u8], ng: u16, nhm: u16, xmins: &Vec<i64>) -> (r: Option<Vec<u8>>)
    requires
        xmins@.len() == ng,
{
    if nhm > ng || nhm < 1 {
        return None;
    }
    let mut h = Rd::new(t);
    let fl = h.u8()?;
    let has_lsb = fl % 2 == 0;
    let has_mono = (fl / 2) % 2 == 0;
    // A transformed table that leaves nothing out is not allowed.
    if has_lsb && has_mono {
        return None;
    }
    let adv = h.take(2 * (nhm as usize))?;
    let lsb = if has_lsb {
        Some(h.take(2 * (nhm as usize))?)
    } else {
        None
    };
    let mono = if has_mono {
        Some(h.take(2 * (ng as usize - nhm as usize))?)
    } else {
        None
    };
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < ng as usize
        invariant
            i <= ng,
            nhm <= ng,
            xmins@.len() == ng,
            adv@.len() == 2 * nhm,
            lsb matches Some(x) ==> x@.len() == 2 * nhm,
            mono matches Some(x) ==> x@.len() == 2 * (ng - nhm),
        decreases ng - i,
    {
        let from_x = if i < nhm as usize {
            append(&mut out, slice(adv, 2 * i, 2 * i + 2));
            match lsb {
                Some(x) => {
                    append(&mut out, slice(x, 2 * i, 2 * i + 2));
                    false
                },
                None => true,
            }
        } else {
            match mono {
                Some(x) => {
                    let j = i - nhm as usize;
                    append(&mut out, slice(x, 2 * j, 2 * j + 2));
                    false
                },
                None => true,
            }
        };
        if from_x {
            let v = xmins[i];
            if v < -32768 || v > 32767 {
                return None;
            }
            put_i16(&mut out, v);
        }
        i += 1;
    }
    Some(out)
}

/// Reads a WOFF2 file (a single font, not a collection) into its tables.
pub fn read_woff2(input: &[u8]) -> (r: Option<Vec<Table>>) {
    if input.len() < 48 || input.len() > MAX_LEN {
        return None;
    }
    // A collection has a second directory that this reader does not handle.
    if rd32(input, 4) == 0x7474_6366 {
        return None;
    }
    let n = rd16(input, 12) as usize;
    let comp_len = rd32(input, 20) as usize;
    let mut d = Rd::new(input);
    let _ = d.take(48)?;
    let mut entries: Vec<Entry> = Vec::new();
    let mut total: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            d.ok(),
            d.s == input,
            total <= MAX_DECOMPRESSED,
            forall|k: int|
                0 <= k < entries@.len() ==> (#[trigger] entries@[k]).off + entries@[k].len <= total,
        decreases n - i,
    {
        let fl = d.u8()?;
        let idx = (fl % 64) as usize;
        let ver = fl / 64;
        let tag = if idx == 63 {
            d.u32()?
        } else {
            known_tag_at(idx)
        };
        let orig = d.base128()? as usize;
        let is_gl = tag == T_GLYF || tag == T_LOCA;
        let xform = if is_gl {
            ver == 0
        } else {
            ver != 0
        };
        // glyf and loca: version 0 is the transform, 3 is none. Others:
        // 0 is none, and only hmtx has a transform (version 1).
        if is_gl && ver != 0 && ver != 3 {
            return None;
        }
        if !is_gl && ver != 0 && !(tag == T_HMTX && ver == 1) {
            return None;
        }
        let len = if xform {
            d.base128()? as usize
        } else {
            orig
        };
        if len > MAX_DECOMPRESSED - total {
            return None;
        }
        entries.push(Entry { tag, xform, off: total, len });
        total = total + len;
        i += 1;
    }
    let src = d.take(comp_len)?;
    let buf = brotli_exact(src, total)?;
    let buf = buf.as_slice();
    // Undo the glyf transform first: hmtx may need the glyphs' xMin.
    let mut ts: Vec<Table> = Vec::new();
    let mut xmins: Option<Vec<i64>> = None;
    let mut ng: u16 = 0;
    let mut long_loca = false;
    let mut i: usize = 0;
    while i < entries.len()
        invariant
            i <= entries@.len(),
            buf@.len() == total,
            forall|k: int|
                0 <= k < entries@.len() ==> (#[trigger] entries@[k]).off + entries@[k].len <= total,
            xmins matches Some(x) ==> x@.len() == ng,
        decreases entries@.len() - i,
    {
        let e = &entries[i];
        if e.tag == T_GLYF && e.xform {
            if xmins.is_some() {
                return None;
            }
            let (glyf, loca, g, xm) = untransform_glyf(slice(buf, e.off, e.off + e.len))?;
            ts.push(Table { tag: T_GLYF, data: glyf });
            ts.push(Table { tag: T_LOCA, data: loca });
            ng = g;
            xmins = Some(xm);
            long_loca = true;
        }
        i += 1;
    }
    let mut hmtx_x: Option<usize> = None;
    let mut i: usize = 0;
    while i < entries.len()
        invariant
            i <= entries@.len(),
            buf@.len() == total,
            forall|k: int|
                0 <= k < entries@.len() ==> (#[trigger] entries@[k]).off + entries@[k].len <= total,
            hmtx_x matches Some(j) ==> j < entries@.len(),
        decreases entries@.len() - i,
    {
        let e = &entries[i];
        if crate::font::is_known_tag(e.tag) {
            if e.xform {
                if e.tag == T_HMTX {
                    hmtx_x = Some(i);
                } else if e.tag == T_LOCA {
                    // The transformed loca is empty: it comes from glyf.
                    if e.len != 0 || !long_loca {
                        return None;
                    }
                }
            } else {
                if lookup(&ts, e.tag).is_some() {
                    return None;
                }
                ts.push(Table { tag: e.tag, data: to_vec(slice(buf, e.off, e.off + e.len)) });
            }
        }
        i += 1;
    }
    match hmtx_x {
        Some(j) => {
            let e = &entries[j];
            let xm = xmins?;
            let hhea = &ts[lookup(&ts, T_HHEA)?].data;
            if hhea.len() < 36 || lookup(&ts, T_HMTX).is_some() {
                return None;
            }
            let nhm = rd16(hhea.as_slice(), 34);
            let data = untransform_hmtx(slice(buf, e.off, e.off + e.len), ng, nhm, &xm)?;
            ts.push(Table { tag: T_HMTX, data });
        },
        None => {},
    }
    // The rebuilt loca is in the long format: say so in head.
    if long_loca {
        let h = lookup(&ts, T_HEAD)?;
        let mut head = to_vec(ts[h].data.as_slice());
        if head.len() < 54 {
            return None;
        }
        set16(&mut head, 50, 1);
        ts.set(h, Table { tag: T_HEAD, data: head });
    }
    Some(ts)
}

} // verus!
