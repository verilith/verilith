//! The PNG container: signature, chunk framing, IHDR, PLTE, tRNS and the
//! IDAT run, proven to compute `spec::chunk_at`, `spec::parse_ihdr` and
//! `spec::walk`.
use crate::spec::*;
use crate::work::Meter;
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_zlib::spec as z;

verus! {

/// The image header (IHDR).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Header {
    pub width: u32,
    pub height: u32,
    pub bit_depth: u8,
    pub color_type: u8,
    pub interlace: u8,
}

impl Header {
    pub open spec fn view(&self) -> Ihdr {
        Ihdr {
            w: self.width as nat,
            h: self.height as nat,
            depth: self.bit_depth as nat,
            ct: self.color_type as nat,
            interlace: self.interlace as nat,
        }
    }
}

/// `spec::be32`.
pub fn read_be32(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r as nat == be32(b@, i as int),
{
    ((b[i] as u32 * 256 + b[i + 1] as u32) * 256 + b[i + 2] as u32) * 256 + b[i + 3] as u32
}

/// `spec::be16`.
pub fn read_be16(b: &[u8], i: usize) -> (r: u16)
    requires
        i + 2 <= b@.len(),
    ensures
        r as nat == be16(b@, i as int),
{
    b[i] as u16 * 256 + b[i + 1] as u16
}

fn is_letter_exec(x: u8) -> (r: bool)
    ensures
        r == is_letter(x),
{
    (65 <= x && x <= 90) || (97 <= x && x <= 122)
}

pub fn is_critical_exec(ty: u32) -> (r: bool)
    ensures
        r == is_critical(ty as nat),
{
    proof {
        assert((ty >> 29u32) & 1u32 == (ty / 0x2000_0000u32) % 2u32) by (bit_vector);
    }
    (ty >> 29) & 1 == 0
}

/// A chunk's length and type, as `spec::chunk_at` reads them, without the
/// CRC check.
pub open spec fn frame_ok(b: Seq<u8>, p: int, len: u32, ty: u32) -> bool {
    &&& chunk_at(b, p) matches Some(c) && c.len == len as nat && c.ty == ty as nat
    &&& p + 12 + len <= b.len()
}

/// Reads the framing of the chunk at `p` (`spec::chunk_at`, except
/// `crc_ok`).
pub fn frame(b: &[u8], p: usize) -> (r: Option<(u32, u32)>)
    ensures
        match r {
            Some((len, ty)) => frame_ok(b@, p as int, len, ty),
            None => chunk_at(b@, p as int) is None,
        },
{
    if p > b.len() || b.len() - p < 12 {
        return None;
    }
    let len = read_be32(b, p);
    if len > 0x7fff_ffff || (b.len() - p - 12) < len as usize {
        return None;
    }
    if !(is_letter_exec(b[p + 4]) && is_letter_exec(b[p + 5]) && 65 <= b[p + 6] && b[p + 6] <= 90
        && is_letter_exec(b[p + 7])) {
        return None;
    }
    let ty = read_be32(b, p + 4);
    Some((len, ty))
}

/// Whether the chunk at `p` with data length `len` has a correct CRC.
pub fn crc_ok(b: &[u8], p: usize, len: u32) -> (r: bool)
    requires
        p + 12 + len <= b@.len(),
    ensures
        r == (be32(b@, p + 8 + len) == z::crc32(b@.subrange(p + 4, p + 8 + len)) as nat),
{
    let _n = b.len();
    let e = p + 8 + len as usize;
    let c = verilith_zlib::checksum::crc32(vstd::slice::slice_subrange(b, p + 4, e));
    let stored = read_be32(b, e);
    stored == c
}

pub fn parse_ihdr_exec(b: &[u8], p: usize, len: u32) -> (r: Option<Header>)
    requires
        p + 8 + len <= b@.len(),
    ensures
        match parse_ihdr(chunk_data(b@, p as int, len as nat)) {
            Some(h) => r matches Some(x) && x.view() == h,
            None => r is None,
        },
{
    let ghost d = chunk_data(b@, p as int, len as nat);
    if len != 13 {
        return None;
    }
    let _n = b.len();
    let q = p + 8;
    proof {
        assert forall|i: int| 0 <= i < 13 implies d[i] == b@[q + i] by {}
    }
    let w = read_be32(b, q);
    let h = read_be32(b, q + 4);
    let depth = b[q + 8];
    let ct = b[q + 9];
    let comp = b[q + 10];
    let filt = b[q + 11];
    let il = b[q + 12];
    let depth_good = if ct == 0 {
        depth == 1 || depth == 2 || depth == 4 || depth == 8 || depth == 16
    } else if ct == 3 {
        depth == 1 || depth == 2 || depth == 4 || depth == 8
    } else if ct == 2 || ct == 4 || ct == 6 {
        depth == 8 || depth == 16
    } else {
        false
    };
    if 1 <= w && w <= 0x7fff_ffff && 1 <= h && h <= 0x7fff_ffff && depth_good && comp == 0
        && filt == 0 && il <= 1 {
        Some(Header { width: w, height: h, bit_depth: depth, color_type: ct, interlace: il })
    } else {
        None
    }
}

/// The walk's state, as offsets into the file.
pub struct WalkX {
    /// Start and length of the palette (length 0 marks a PLTE seen in a
    /// non-palette image).
    pub plte: Option<(usize, usize)>,
    /// Start and length of the accepted tRNS data.
    pub trns: Option<(usize, usize)>,
    /// Start and length of each IDAT chunk's data in the first run.
    pub idat: Vec<(usize, usize)>,
    pub phase: u8,
    pub bkgd: bool,
}

pub open spec fn range(b: Seq<u8>, r: (usize, usize)) -> Seq<u8> {
    b.subrange(r.0 as int, r.0 + r.1)
}

/// The concatenated data of the first `n` ranges.
pub open spec fn concat(b: Seq<u8>, rs: Seq<(usize, usize)>, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        concat(b, rs, (n - 1) as nat) + range(b, rs[n - 1])
    }
}

/// The IDAT data gathered so far, plus 12 for each chunk: at most the
/// bytes of the file the walk has passed.
pub open spec fn idat_cost(b: Seq<u8>, rs: Seq<(usize, usize)>) -> nat {
    concat(b, rs, rs.len()).len() + 12 * rs.len()
}

pub open spec fn ranges_ok(b: Seq<u8>, rs: Seq<(usize, usize)>) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i].0 + rs[i].1 <= b.len()
}

impl WalkX {
    pub open spec fn wf(&self, b: Seq<u8>) -> bool {
        &&& self.plte matches Some(r) ==> r.0 + r.1 <= b.len() && r.1 <= 768
        &&& self.trns matches Some(r) ==> r.0 + r.1 <= b.len() && r.1 <= 256
        &&& ranges_ok(b, self.idat@)
        &&& self.phase <= 2
    }

    pub open spec fn view(&self, b: Seq<u8>) -> Walk {
        Walk {
            plte: match self.plte {
                Some(r) => Some(range(b, r)),
                None => None,
            },
            trns: match self.trns {
                Some(r) => Some(range(b, r)),
                None => None,
            },
            idat: concat(b, self.idat@, self.idat@.len()),
            phase: self.phase as nat,
            bkgd: self.bkgd,
        }
    }
}

/// One step of the walk (`spec::step`) for the chunk at `p`: updates the
/// state, or returns `Err(true)` at IEND (leaving it unchanged) and
/// `Err(false)` on an error.
#[verifier::rlimit(40)]
fn step_exec(b: &[u8], h: &Header, p: usize, len: u32, ty: u32, st: &mut WalkX, Tracked(m): Tracked<&mut Meter>) -> (r: Result<
    (),
    bool,
>)
    requires
        frame_ok(b@, p as int, len, ty),
        old(st).wf(b@),
        depth_ok(h.view().ct, h.view().depth),
    ensures
        final(m).n <= old(m).n + len + 8,
        idat_cost(b@, final(st).idat@) <= idat_cost(b@, old(st).idat@) + 12 + len,
        final(st).wf(b@),
        match step(b@, h.view(), p as int, chunk_at(b@, p as int).unwrap(), old(st).view(b@)) {
            Ok(s2) => r == Ok::<(), bool>(()) && final(st).view(b@) == s2,
            Err(true) => r == Err::<(), bool>(true) && final(st).view(b@) == old(st).view(b@),
            Err(false) => r == Err::<(), bool>(false),
        },
{
    let ghost hv = h.view();
    let _n = b.len();
    let ds = p + 8;
    let dl = len as usize;
    // The CRC, over the type and the data, and a step for the rest.
    proof {
        m.n = (m.n + len + 8) as nat;
    }
    proof {
        assert(range(b@, (ds, dl)) == chunk_data(b@, p as int, len as nat));
    }
    if ty == 0x4945_4e44 {
        return if st.phase == 0 {
            Err(false)
        } else {
            Err(true)
        };
    }
    let critical = is_critical_exec(ty);
    // Only critical chunks, tRNS and bKGD need their CRC: any other chunk is
    // skipped whether or not it is correct.
    if critical || ty == 0x7452_4e53 || ty == 0x624b_4744 {
        if !crc_ok(b, p, len) {
            if critical && !(ty == 0x504c_5445 && h.color_type != 3 && st.phase == 0) {
                return Err(false);
            } else {
                if st.phase == 1 {
                    st.phase = 2;
                }
                return Ok(());
            }
        }
    }
    if ty == 0x4944_4154 {
        if st.phase == 0 {
            if h.color_type == 3 && st.plte.is_none() {
                return Err(false);
            }
            st.idat = Vec::new();
            st.idat.push((ds, dl));
            st.phase = 1;
            proof {
                assert(st.idat@.len() == 1);
                reveal_with_fuel(concat, 2);
                assert(concat(b@, st.idat@, 1).len() == dl);
                assert(concat(b@, st.idat@, 0) =~= Seq::<u8>::empty());
                assert(st.view(b@).idat =~= chunk_data(b@, p as int, len as nat));
            }
            return Ok(());
        } else if st.phase == 1 {
            let ghost old_idat = st.idat@;
            st.idat.push((ds, dl));
            proof {
                assert(st.idat@.subrange(0, old_idat.len() as int) =~= old_idat);
                lemma_concat_prefix(b@, st.idat@, old_idat, old_idat.len());
                assert(concat(b@, st.idat@, st.idat@.len()).len() == concat(b@, old_idat, old_idat.len()).len() + dl);
                assert(ranges_ok(b@, st.idat@)) by {
                    assert forall|i: int| 0 <= i < st.idat@.len() implies #[trigger] st.idat@[i].0
                        + st.idat@[i].1 <= b@.len() by {
                        if i < old_idat.len() {
                            assert(st.idat@[i] == old_idat[i]);
                        }
                    }
                }
            }
            return Ok(());
        } else {
            return Ok(());
        }
    }
    // Any chunk other than IDAT ends the first IDAT run.
    if st.phase == 1 {
        st.phase = 2;
    }
    if ty == 0x4948_4452 {
        Err(false)
    } else if ty == 0x504c_5445 {
        if st.phase != 0 {
            return Ok(());
        }
        if h.color_type == 3 {
            if st.plte.is_some() || dl % 3 != 0 || dl == 0 || dl > 768 {
                return Err(false);
            }
            proof {
                reveal_with_fuel(pow2_nat, 9);
            }
            let max: usize = if h.bit_depth == 1 {
                2
            } else if h.bit_depth == 2 {
                4
            } else if h.bit_depth == 4 {
                16
            } else {
                256
            };
            let n = if dl / 3 > max {
                3 * max
            } else {
                dl
            };
            st.plte = Some((ds, n));
            proof {
                assert(range(b@, (ds, n)) =~= take_plte(hv, chunk_data(b@, p as int, len as nat)));
            }
            Ok(())
        } else if h.color_type == 2 || h.color_type == 6 {
            if st.plte.is_some() || st.trns.is_some() || st.bkgd || dl % 3 != 0 || dl > 768 {
                Ok(())
            } else if dl == 0 {
                Err(false)
            } else {
                st.plte = Some((ds, 0));
                proof {
                    assert(range(b@, (ds, 0usize)) =~= Seq::<u8>::empty());
                }
                Ok(())
            }
        } else {
            Ok(())
        }
    } else if ty == 0x624b_4744 {
        if st.phase == 0 && (h.color_type == 2 || h.color_type == 6) && dl == 6 {
            st.bkgd = true;
        }
        Ok(())
    } else if ty == 0x7452_4e53 {
        let ok = st.trns.is_none() && st.phase == 0 && if h.color_type == 0 {
            dl == 2
        } else if h.color_type == 2 {
            dl == 6
        } else if h.color_type == 3 {
            match st.plte {
                Some((_, pl)) => 1 <= dl && dl <= pl / 3,
                None => false,
            }
        } else {
            false
        };
        if ok {
            st.trns = Some((ds, dl));
        }
        Ok(())
    } else if critical {
        if st.phase == 0 {
            Err(false)
        } else {
            Ok(())
        }
    } else {
        Ok(())
    }
}

pub proof fn lemma_concat_prefix(b: Seq<u8>, rs: Seq<(usize, usize)>, qs: Seq<(usize, usize)>, n: nat)
    requires
        n <= qs.len(),
        n <= rs.len(),
        forall|i: int| 0 <= i < n ==> rs[i] == qs[i],
    ensures
        concat(b, rs, n) == concat(b, qs, n),
    decreases n,
{
    if n > 0 {
        lemma_concat_prefix(b, rs, qs, (n - 1) as nat);
    }
}

/// Walks the chunks from `p` to IEND (`spec::walk`).
/// Counts at most a step for each byte from `p` on.
pub fn walk_exec(b: &[u8], h: &Header, p: usize, Tracked(m): Tracked<&mut Meter>) -> (r: Option<WalkX>)
    requires
        depth_ok(h.view().ct, h.view().depth),
    ensures
        match walk(b@, h.view(), p as int, walk_start()) {
            Some(s) => r matches Some(x) && x.wf(b@) && x.view(b@) == s,
            None => r is None,
        },
        final(m).n <= old(m).n + b@.len(),
        r matches Some(x) ==> idat_cost(b@, x.idat@) <= b@.len(),
{
    let ghost m0 = m.n;
    let mut st = WalkX { plte: None, trns: None, idat: Vec::new(), phase: 0, bkgd: false };
    let mut q = p;
    proof {
        assert(st.view(b@) =~= walk_start());
    }
    let ghost goal = walk(b@, h.view(), p as int, walk_start());
    loop
        invariant
            st.wf(b@),
            depth_ok(h.view().ct, h.view().depth),
            goal == walk(b@, h.view(), p as int, walk_start()),
            walk(b@, h.view(), q as int, st.view(b@)) == goal,
            p <= q,
            q <= b@.len() || q == p,
            m.n + p <= m0 + q,
            m0 == old(m).n,
            idat_cost(b@, st.idat@) + p <= q,
        decreases b@.len() - q,
    {
        let (len, ty) = match frame(b, q) {
            Some(f) => f,
            None => {
                assert(chunk_at(b@, q as int) is None);
                assert(walk(b@, h.view(), q as int, st.view(b@)) is None);
                return None;
            },
        };
        let _n = b.len();
        match step_exec(b, h, q, len, ty, &mut st, Tracked(m)) {
            Err(true) => return Some(st),
            Err(false) => return None,
            Ok(()) => {
                q = q + 12 + len as usize;
            },
        }
    }
}

pub open spec fn plte_inv(h: Ihdr, st: Walk) -> bool {
    &&& st.phase != 0 && h.ct == 3 ==> st.plte is Some
    &&& st.trns matches Some(t) ==> trns_len_ok(h, t)
    &&& st.plte matches Some(p) ==> p.len() <= 768
}

/// An accepted tRNS chunk's length fits its colour type.
pub open spec fn trns_len_ok(h: Ihdr, t: Seq<u8>) -> bool {
    &&& h.ct == 0 ==> t.len() == 2
    &&& h.ct == 2 ==> t.len() == 6
    &&& h.ct != 0 && h.ct != 2 ==> h.ct == 3 && t.len() <= 256
}

/// A finished walk has seen IDAT, and PLTE before it in a palette image.
pub proof fn lemma_walk_plte(b: Seq<u8>, h: Ihdr, p: int, st: Walk)
    requires
        plte_inv(h, st),
    ensures
        walk(b, h, p, st) matches Some(s) ==> s.phase != 0 && plte_inv(h, s),
    decreases b.len() - p,
{
    if let Some(c) = chunk_at(b, p) {
        match step(b, h, p, c, st) {
            Ok(s2) => {
                assert(plte_inv(h, s2));
                if p + 12 + c.len <= b.len() {
                    lemma_walk_plte(b, h, p + 12 + c.len, s2);
                }
            },
            _ => {},
        }
    }
}

} // verus!
