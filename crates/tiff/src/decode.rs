//! The decoder's entry point, proven to compute `spec::decode`.
use crate::chunk::*;
use crate::ifd::*;
#[cfg(verus_only)]
use crate::lzw::STORED;
use crate::params::*;
use crate::place::*;
use crate::predict::unpredict_exec;
use crate::prims::alloc_zeroed;
use crate::spec;
use crate::spec::*;
use verilith_core::prims::{alloc_u32, copy_in, get};
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::mul::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A decoded image (`spec::Image`).
#[derive(Debug)]
pub struct Tiff {
    /// Whether the file is little-endian ("II").
    pub le: bool,
    pub width: u32,
    pub height: u32,
    pub bits_per_sample: u32,
    pub samples_per_pixel: u32,
    pub compression: u32,
    pub photometric: u32,
    /// 1 unsigned, 2 signed, 3 floating point, 4 undefined.
    pub sample_format: u32,
    /// 1: the samples of a pixel are together; 2: one plane per sample.
    pub planar: u32,
    /// Each plane in turn (one, or one per sample if `planar` is 2), each
    /// `height` rows of `ceil(width * samples * bits_per_sample / 8)`
    /// bytes, where `samples` is the samples per pixel in a plane. Samples
    /// of fewer than 8 bits are packed from the most significant bit; those
    /// of 16, 24 and 32 bits are little-endian.
    pub pixels: Vec<u8>,
}

impl Tiff {
    pub open spec fn view(self) -> spec::Image {
        spec::Image {
            le: self.le,
            width: self.width as nat,
            height: self.height as nat,
            bits_per_sample: self.bits_per_sample as nat,
            samples_per_pixel: self.samples_per_pixel as nat,
            compression: self.compression as nat,
            photometric: self.photometric as nat,
            sample_format: self.sample_format as nat,
            planar: self.planar as nat,
            pixels: self.pixels@,
        }
    }
}

/// Bytes in a row of the image, in one plane (`Params::row_bytes`).
fn row_bytes_exec(p: &ParamsX, Ghost(b): Ghost<Seq<u8>>) -> (r: u128)
    requires
        p.view(b).wf(),
    ensures
        r as nat == p.view(b).row_bytes(),
        r <= 0x10_0000_0000_0000_0000,
{
    let sc: u128 = if p.planar == 2 { 1 } else { p.spp as u128 };
    proof {
        lemma_mul_inequality(p.width as int, u32::MAX as int, sc as int);
        lemma_mul_inequality(sc as int, u32::MAX as int, u32::MAX as int);
        lemma_mul_is_commutative(p.width as int, sc as int);
        lemma_mul_inequality((p.width as int * sc as int), 0xffff_ffff_ffff_ffff, p.bps as int);
        lemma_mul_inequality(p.bps as int, 32, 0xffff_ffff_ffff_ffff);
        lemma_mul_is_commutative((p.width as int * sc as int), p.bps as int);
    }
    let e = p.width as u128 * sc * p.bps as u128;
    (e + 7) / 8
}

/// Bytes per row of a strip or tile (`Params::chunk_row_bytes`).
fn chunk_row_bytes_exec(p: &ParamsX, Ghost(b): Ghost<Seq<u8>>) -> (r: u128)
    requires
        p.view(b).wf(),
    ensures
        r as nat == p.view(b).chunk_row_bytes(),
        r <= 0x10_0000_0000_0000_0000,
{
    if p.tiled {
        let sc: u128 = if p.planar == 2 { 1 } else { p.spp as u128 };
        proof {
            lemma_mul_inequality(p.tw as int, u32::MAX as int, sc as int);
            lemma_mul_inequality(sc as int, u32::MAX as int, u32::MAX as int);
            lemma_mul_is_commutative(p.tw as int, sc as int);
            lemma_mul_inequality((p.tw as int * sc as int), 0xffff_ffff_ffff_ffff, p.bps as int);
            lemma_mul_inequality(p.bps as int, 32, 0xffff_ffff_ffff_ffff);
            lemma_mul_is_commutative((p.tw as int * sc as int), p.bps as int);
        }
        p.tw as u128 * sc * p.bps as u128 / 8
    } else {
        row_bytes_exec(p, Ghost(b))
    }
}

/// Rows in strip or tile `k` (`Params::chunk_rows`).
fn chunk_rows_exec(p: &ParamsX, k: u64, Ghost(b): Ghost<Seq<u8>>) -> (r: u64)
    requires
        p.view(b).wf(),
    ensures
        r as nat == p.view(b).chunk_rows(k as nat),
        r <= u32::MAX,
{
    if p.tiled {
        p.th as u64
    } else {
        let s = div_up_exec(p.height as u64, p.rps as u64);
        proof {
            lemma_div_up(p.height as int, p.rps as int, 0);
        }
        let j = k % s;
        proof {
            lemma_mul_inequality(j as int + 1, s as int, p.rps as int);
            lemma_mul_inequality(s as int, p.height as int, p.rps as int);
            lemma_mul_inequality(p.height as int, u32::MAX as int, p.rps as int);
        }
        if (j + 1) as u128 * p.rps as u128 <= p.height as u128 {
            p.rps as u64
        } else {
            proof {
                lemma_mod_bound(k as int, s as int);
                lemma_div_up(p.height as int, p.rps as int, j as int);
            }
            p.height as u64 - (j as u128 * p.rps as u128) as u64
        }
    }
}

/// A row size that is a whole number of `k`-byte samples.
proof fn lemma_whole_samples(p: Params)
    requires
        p.wf(),
        p.bps % 8 == 0,
    ensures
        p.chunk_row_bytes() % (p.bps / 8) == 0,
        p.chunk_row_bytes() >= 1,
        p.chunk_row_bytes() == p.chunk_width() * p.sc() * (p.bps / 8),
{
    let m = (p.bps / 8) as int;
    assert(p.bps == 8 * m);
    lemma_row_bytes_pos(p);
    let cw = p.chunk_width() as int;
    let a = cw * p.sc() as int * m;
    assert(cw * p.sc() as int * p.bps as int == 8 * a) by {
        lemma_mul_is_associative(cw * p.sc() as int, 8, m);
        lemma_mul_is_commutative(cw * p.sc() as int, 8);
        lemma_mul_is_associative(8, cw * p.sc() as int, m);
    }
    lemma_fundamental_div_mod_converse(8 * a, 8, a, 0);
    lemma_fundamental_div_mod_converse(8 * a + 7, 8, a, 7);
    lemma_mod_multiples_basic(cw * p.sc() as int, m);
    assert(cw >= 1) by {
        if p.tiled {} else {}
    }
    lemma_mul_inequality(1, cw, p.sc() as int);
    lemma_mul_inequality(1, cw * p.sc() as int, m);
}

proof fn lemma_mod_mul(rows: int, rb: int, m: int)
    requires
        rows >= 0,
        rb >= 1,
        m >= 1,
        rb % m == 0,
    ensures
        (rows * rb) % rb == 0,
        (rows * rb) % m == 0,
{
    lemma_mod_multiples_basic(rows, rb);
    lemma_fundamental_div_mod(rb, m);
    let q = rb / m;
    assert(rows * rb == (rows * q) * m) by {
        lemma_mul_is_associative(rows, q, m);
        lemma_mul_is_commutative(m, q);
    }
    lemma_mod_multiples_basic(rows * q, m);
}

/// A strip or tile after decompression: made little-endian and with the
/// predictor undone, as `spec::chunk` does.
pub open spec fn post(p: Params, d: Seq<u8>) -> Seq<u8> {
    let d = to_le(p, d);
    if p.predictor == 2 {
        unpredict(d, p.chunk_row_bytes(), p.bps / 8, p.sc())
    } else {
        d
    }
}

proof fn lemma_chunk(b: Seq<u8>, p: Params, k: nat)
    ensures
        chunk(b, p, k) == ({
            let off = p.offsets[k as int];
            let cnt = p.counts[k as int];
            if off + cnt > b.len() {
                None
            } else {
                match decompress(p.compression, b.subrange(off as int, (off + cnt) as int), p.chunk_size(k), p.chunk_row_bytes()) {
                    None => None,
                    Some(d) => Some(post(p, d)),
                }
            }
        }),
{
    reveal(chunk);
}

/// Bytes strip or tile `k` decodes to (`Params::chunk_size`).
fn chunk_size_exec(p: &ParamsX, k: u32, Ghost(b): Ghost<Seq<u8>>) -> (r: (u128, u64, u128))
    requires
        p.view(b).wf(),
    ensures
        r.0 as nat == p.view(b).chunk_size(k as nat),
        r.1 as nat == p.view(b).chunk_rows(k as nat),
        r.2 as nat == p.view(b).chunk_row_bytes(),
{
    let rows = chunk_rows_exec(p, k as u64, Ghost(b));
    let crb = chunk_row_bytes_exec(p, Ghost(b));
    proof {
        lemma_mul_inequality(rows as int, u32::MAX as int, crb as int);
        lemma_mul_inequality(crb as int, 0x10_0000_0000_0000_0000, u32::MAX as int);
        lemma_mul_is_commutative(rows as int, crb as int);
    }
    (rows as u128 * crb, rows, crb)
}

/// `post`, in place.
fn post_exec(v: &mut Vec<u8>, p: &ParamsX, rows: u64, crb: u128, Ghost(b): Ghost<Seq<u8>>)
    requires
        p.view(b).wf(),
        crb as nat == p.view(b).chunk_row_bytes(),
        rows >= 1,
        old(v)@.len() == rows * crb,
    ensures
        final(v)@ == post(p.view(b), old(v)@),
{
    let ghost pv = p.view(b);
    let ghost d0 = v@;
    let vl = v.len();
    proof {
        lemma_mul_inequality(1, rows as int, crb as int);
    }
    if !p.le && (p.bps == 16 || p.bps == 24 || p.bps == 32) {
        proof {
            lemma_whole_samples(pv);
            lemma_mod_mul(rows as int, crb as int, (p.bps / 8) as int);
        }
        swap_exec(v.as_mut_slice(), (p.bps / 8) as usize);
    }
    proof {
        assert(v@ =~= to_le(pv, d0));
    }
    if p.predictor == 2 {
        proof {
            lemma_whole_samples(pv);
            lemma_mod_mul(rows as int, crb as int, (p.bps / 8) as int);
        }
        let sc: usize = if p.planar == 2 { 1 } else { p.spp as usize };
        unpredict_exec(v.as_mut_slice(), crb as usize, (p.bps / 8) as usize, sc);
    }
}

/// Strip or tile `k`, decoded (`spec::chunk`).
pub fn chunk_exec(b: &[u8], p: &ParamsX, k: u32, limit: usize, off: &mut [u32], len: &mut [u32]) -> (r: Result<Vec<u8>, Error>)
    requires
        p.view(b@).wf(),
        p.ok(b@),
        k < p.offsets.count,
        k < p.counts.count,
        old(off)@.len() == STORED,
        old(len)@.len() == STORED,
    ensures
        final(off)@.len() == STORED,
        final(len)@.len() == STORED,
        match r {
            Ok(v) => chunk(b@, p.view(b@), k as nat) == Some(v@) && v@.len() == p.view(b@).chunk_size(k as nat),
            Err(Error::Invalid) => chunk(b@, p.view(b@), k as nat) is None,
            Err(Error::Unsupported) => false,
            Err(_) => true,
        },
{
    let ghost pv = p.view(b@);
    proof {
        lemma_chunk(b@, pv, k as nat);
    }
    let o = value_exec(b, p.le, p.offsets, k) as u64;
    let c = value_exec(b, p.le, p.counts, k) as u64;
    if o + c > b.len() as u64 {
        return Err(Error::Invalid);
    }
    let (size, rows, crb) = chunk_size_exec(p, k, Ghost(b@));
    if size > limit as u128 {
        return Err(Error::TooLarge);
    }
    let data = slice_subrange(b, o as usize, (o + c) as usize);
    proof {
        lemma_chunk_size_pos(pv, k as nat);
        lemma_mul_inequality(1, rows as int, crb as int);
        lemma_mod_multiples_basic(rows as int, crb as int);
    }
    let mut v = match decompress_exec(p.compression, data, size as usize, crb as usize, off, len) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    post_exec(&mut v, p, rows, crb, Ghost(b@));
    Ok(v)
}

/// Bytes of the output that are right: those whose strip or tile, by
/// `owner`, comes before `upto`.
pub open spec fn placed(b: Seq<u8>, p: Params, out: Seq<u8>, upto: int) -> bool {
    forall|i: int|
        0 <= i < p.image_size() && #[trigger] owner(p, i).0 < upto ==> out[i] == chunk(b, p, owner(p, i).0 as nat)->Some_0[owner(p, i).1]
}

/// `copy_in`, with what it does stated byte by byte.
fn copy_at(out: &mut [u8], dst: usize, src: &[u8], s: usize, n: usize)
    requires
        s + n <= src@.len(),
        dst + n <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < final(out)@.len() ==> #[trigger] final(out)@[i] == if dst <= i < dst + n {
            src@[s + i - dst]
        } else {
            old(out)@[i]
        },
{
    let ghost o = out@;
    copy_in(out, dst, src, s, n);
    proof {
        assert forall|i: int| 0 <= i < out@.len() implies #[trigger] out@[i] == if dst <= i < dst + n {
            src@[s + i - dst]
        } else {
            o[i]
        } by {
            if i < dst {
                assert(out@[i] == o.subrange(0, dst as int)[i]);
            } else if i < dst + n {
                assert(out@[i] == src@.subrange(s as int, s + n)[i - dst]);
            } else {
                assert(out@[i] == o.subrange(dst + n, o.len() as int)[i - dst - n]);
            }
        }
    }
}

/// Every strip or tile decodes to at least one byte.
proof fn lemma_chunk_size_pos(p: Params, k: nat)
    requires
        p.wf(),
    ensures
        p.chunk_size(k) >= 1,
        p.chunk_row_bytes() >= 1,
        p.chunk_rows(k) >= 1,
{
    lemma_row_bytes_pos(p);
    if p.tiled {
        lemma_mul_inequality(1, p.tw as int, p.sc() as int);
        lemma_mul_inequality(1, (p.tw * p.sc()) as int, p.bps as int);
        lemma_fundamental_div_mod((p.tw * p.sc() * p.bps) as int, 8);
    } else {
        lemma_div_up(p.height as int, p.rps as int, 0);
        let s = p.strips() as int;
        lemma_mod_bound(k as int, s);
        lemma_div_up(p.height as int, p.rps as int, k as int % s);
    }
    lemma_mul_inequality(1, p.chunk_rows(k) as int, p.chunk_row_bytes() as int);
}

/// Where strip `k` starts (`Params::strip_start`).
fn strip_start_exec(p: &ParamsX, k: u32, Ghost(b): Ghost<Seq<u8>>) -> (r: u128)
    requires
        p.view(b).wf(),
        !p.tiled,
        (k as nat) < p.view(b).chunks(),
        p.view(b).image_size() <= u64::MAX,
    ensures
        r as nat == p.view(b).strip_start(k as nat),
{
    let ghost pv = p.view(b);
    let rb = row_bytes_exec(p, Ghost(b));
    let s = div_up_exec(p.height as u64, p.rps as u64) as u128;
    proof {
        lemma_chunk_size_pos(pv, k as nat);
        lemma_strip_a(pv, k as nat, 0);
        lemma_div_up(p.height as int, p.rps as int, 0);
        lemma_mul_inequality(p.rps as int, u32::MAX as int, rb as int);
        lemma_mul_inequality(rb as int, 0x10_0000_0000_0000_0000, u32::MAX as int);
        lemma_mul_is_commutative(p.rps as int, rb as int);
        lemma_mul_inequality(p.height as int, u32::MAX as int, rb as int);
        lemma_mul_is_commutative(p.height as int, rb as int);
        lemma_mul_nonnegative(k as int / s as int, (p.height * rb) as int);
        lemma_mul_nonnegative(k as int % s as int, (p.rps * rb) as int);
    }
    let ps = p.height as u128 * rb;
    let big_r = p.rps as u128 * rb;
    (k as u128 / s) * ps + (k as u128 % s) * big_r
}

/// Copies strip `k` into the output.
fn place_strip(out: &mut [u8], v: &[u8], p: &ParamsX, k: u32, Ghost(b): Ghost<Seq<u8>>)
    requires
        p.view(b).wf(),
        !p.tiled,
        old(out)@.len() == p.view(b).image_size(),
        p.view(b).image_size() <= u64::MAX,
        (k as nat) < p.view(b).chunks(),
        chunk(b, p.view(b), k as nat) == Some(v@),
        v@.len() == p.view(b).chunk_size(k as nat),
        placed(b, p.view(b), old(out)@, k as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        placed(b, p.view(b), final(out)@, k + 1),
{
    let ghost pv = p.view(b);
    let ghost o = out@;
    let start = strip_start_exec(p, k, Ghost(b));
    proof {
        lemma_chunk_size_pos(pv, k as nat);
        lemma_strip_a(pv, k as nat, (v@.len() - 1) as nat);
    }
    let n = v.len();
    let ol = out.len();
    copy_at(out, start as usize, v, 0, n);
    proof {
        assert forall|i: int|
            0 <= i < pv.image_size() && #[trigger] owner(pv, i).0 < k + 1 implies out@[i] == chunk(b, pv, owner(pv, i).0 as nat)->Some_0[owner(pv, i).1] by {
            if start <= i < start + n {
                lemma_strip_a(pv, k as nat, (i - start) as nat);
            } else {
                lemma_strip_b(pv, i);
            }
        }
    }
}

/// Where row `yy` of tile `k` goes, and how many of its bytes do
/// (`Params::tile_dst`, `Params::tile_len`), and the tile's first row
/// (`Params::tile_y`).
fn tile_geom_exec(p: &ParamsX, k: u32, Ghost(b): Ghost<Seq<u8>>) -> (r: (u128, u128, u128, u128, u128))
    requires
        p.view(b).wf(),
        p.tiled,
        (k as nat) < p.view(b).chunks(),
        p.view(b).image_size() <= u64::MAX,
    ensures
        ({
            let (base, ystep, ty, len, rb) = r;
            &&& ty as nat == p.view(b).tile_y(k as nat)
            &&& ty < p.height
            &&& len as nat == p.view(b).tile_len(k as nat)
            &&& rb as nat == p.view(b).row_bytes()
            &&& ystep == rb
            &&& forall|yy: nat| yy < p.th && ty + yy < p.height ==> base + (ty + yy) * rb == p.view(b).tile_dst(k as nat, yy)
            &&& 1 <= len
            &&& len <= p.view(b).tile_row_bytes()
        }),
{
    let ghost pv = p.view(b);
    let rb = row_bytes_exec(p, Ghost(b));
    let trb = chunk_row_bytes_exec(p, Ghost(b));
    let ta = div_up_exec(p.width as u64, p.tw as u64) as u128;
    let td = div_up_exec(p.height as u64, p.th as u64) as u128;
    proof {
        lemma_div_up(p.width as int, p.tw as int, 0);
        lemma_div_up(p.height as int, p.th as int, 0);
        lemma_mul_inequality(ta as int, u32::MAX as int, td as int);
        lemma_mul_inequality(td as int, u32::MAX as int, u32::MAX as int);
        lemma_mul_is_commutative(ta as int, td as int);
        lemma_mul_inequality(1, ta as int, td as int);
        lemma_row_bytes_pos(pv);
        lemma_chunk_size_pos(pv, k as nat);
    }
    let t = ta * td;
    let pl = k as u128 / t;
    let m = k as u128 % t;
    let ty = m / ta;
    let tx = m % ta;
    proof {
        lemma_mod_bound(m as int, ta as int);
        lemma_mod_bound(k as int, t as int);
        lemma_div_pos_is_pos(m as int, ta as int);
        lemma_multiply_divide_lt(m as int, ta as int, td as int);
        // The tile's first byte is inside the output: tile_a at (0, 0).
        lemma_tile_starts_pub(pv, tx as int);
        lemma_div_up(p.height as int, p.th as int, ty as int);
        lemma_mul_is_commutative(ty as int, p.th as int);
        lemma_tile_a(pv, k as nat, 0, 0);
        lemma_mul_nonnegative(pl as int, (p.height * rb) as int);
        lemma_mul_nonnegative(ty as int * p.th as int, rb as int);
        lemma_mul_nonnegative(tx as int, trb as int);
        lemma_mul_inequality(p.height as int, u32::MAX as int, rb as int);
        lemma_mul_inequality(rb as int, 0x10_0000_0000_0000_0000, u32::MAX as int);
        lemma_mul_is_commutative(p.height as int, rb as int);
    }
    let ps = p.height as u128 * rb;
    let y0 = ty * p.th as u128;
    let base = pl * ps + tx * trb;
    let left = rb - tx * trb;
    let len = if trb <= left { trb } else { left };
    proof {
        assert forall|yy: nat| yy < p.th && y0 + yy < p.height implies base + (y0 + yy) * rb == pv.tile_dst(k as nat, yy) by {
            lemma_mul_is_distributive_add_other_way(rb as int, y0 as int, yy as int);
        }
    }
    (base, rb, y0, len, rb)
}

/// Copies tile `k` into the output, a row at a time.
fn place_tile(out: &mut [u8], v: &[u8], p: &ParamsX, k: u32, Ghost(b): Ghost<Seq<u8>>)
    requires
        p.view(b).wf(),
        p.tiled,
        old(out)@.len() == p.view(b).image_size(),
        p.view(b).image_size() <= u64::MAX,
        (k as nat) < p.view(b).chunks(),
        chunk(b, p.view(b), k as nat) == Some(v@),
        v@.len() == p.view(b).chunk_size(k as nat),
        placed(b, p.view(b), old(out)@, k as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        placed(b, p.view(b), final(out)@, k + 1),
{
    let ghost pv = p.view(b);
    let (base, ystep, y0, tlen, rb) = tile_geom_exec(p, k, Ghost(b));
    let trb = chunk_row_bytes_exec(p, Ghost(b));
    let th = p.th as u128;
    let h = p.height as u128;
    let vl = v.len();
    let ol = out.len();
    proof {
        lemma_mul_is_commutative(th as int, trb as int);
    }
    let mut yy: u128 = 0;
    while yy < th && y0 + yy < h
        invariant
            pv == p.view(b),
            pv.wf(),
            p.tiled,
            out@.len() == pv.image_size(),
            pv.image_size() <= u64::MAX,
            (k as nat) < pv.chunks(),
            chunk(b, pv, k as nat) == Some(v@),
            v@.len() == pv.chunk_size(k as nat),
            trb as nat == pv.tile_row_bytes(),
            th == p.th,
            h == p.height,
            y0 as nat == pv.tile_y(k as nat),
            tlen as nat == pv.tile_len(k as nat),
            1 <= tlen <= trb,
            vl == v@.len(),
            ol == out@.len(),
            y0 < h,
            forall|y: nat| y < p.th && y0 + y < p.height ==> base + (y0 + y) * rb == pv.tile_dst(k as nat, y),
            yy <= th,
            forall|i: int|
                0 <= i < pv.image_size() && #[trigger] owner(pv, i).0 < k + 1 && (owner(pv, i).0 < k
                    || (0 <= owner(pv, i).1 && owner(pv, i).1 / (trb as int) < yy)) ==> out@[i] == chunk(b, pv, owner(pv, i).0 as nat)->Some_0[owner(pv, i).1],
        decreases th - yy,
    {
        let ghost o = out@;
        proof {
            lemma_tile_a(pv, k as nat, yy as nat, (tlen - 1) as nat);
            lemma_mul_inequality(yy as int + 1, th as int, trb as int);
            lemma_mul_is_distributive_add_other_way(trb as int, yy as int, 1);
            lemma_mul_is_commutative(th as int, trb as int);
            lemma_mul_is_commutative(trb as int, yy as int);
            lemma_mul_is_commutative(trb as int, yy as int + 1);
            lemma_mul_nonnegative(yy as int, trb as int);
        }
        proof {
            assert(base + (y0 + yy) * rb == pv.tile_dst(k as nat, yy as nat));
        }
        let dst = base + (y0 + yy) * rb;
        let src = yy * trb;
        copy_at(out, dst as usize, v, src as usize, tlen as usize);
        proof {
            let trbi = trb as int;
            assert forall|i: int|
                0 <= i < pv.image_size() && #[trigger] owner(pv, i).0 < k + 1 && (owner(pv, i).0 < k
                    || (0 <= owner(pv, i).1 && owner(pv, i).1 / trbi < yy + 1)) implies out@[i] == chunk(b, pv, owner(pv, i).0 as nat)->Some_0[owner(pv, i).1] by {
                if dst <= i < dst + tlen {
                    let xx = (i - dst) as nat;
                    lemma_tile_a(pv, k as nat, yy as nat, xx);
                    lemma_fundamental_div_mod_converse((yy * trb + xx) as int, trbi, yy as int, xx as int);
                } else {
                    lemma_tile_b(pv, i);
                    if owner(pv, i).0 == k && owner(pv, i).1 / trbi == yy {
                        assert(false);
                    }
                }
            }
        }
        yy = yy + 1;
    }
    proof {
        let trbi = trb as int;
        assert forall|i: int|
            0 <= i < pv.image_size() && #[trigger] owner(pv, i).0 < k + 1 implies out@[i] == chunk(b, pv, owner(pv, i).0 as nat)->Some_0[owner(pv, i).1] by {
            if owner(pv, i).0 == k {
                lemma_tile_b(pv, i);
            }
        }
    }
}

/// `spec::first` of a field.
fn first_exec(b: &[u8], le: bool, o: usize, n: usize, tag: u16) -> (r: Option<u32>)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        match first(field(b@, le, o as nat, n as nat, tag as nat)) {
            Some(x) => r == Some(x as u32) && x <= u32::MAX,
            None => r is None,
        },
{
    match field_exec(b, le, o, n, tag) {
        Ok(Some(f)) => if f.count >= 1 {
            Some(value_exec(b, le, f, 0))
        } else {
            None
        },
        _ => None,
    }
}

/// `spec::unsupported_ifd`.
fn unsupported_ifd_exec(b: &[u8], le: bool, o: usize, n: usize) -> (r: bool)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        r == unsupported_ifd(b@, le, o as nat, n as nat),
{
    let comp = first_exec(b, le, o, n, 259);
    let pred = first_exec(b, le, o, n, 317);
    let ghost bv = match field(b@, le, o as nat, n as nat, BITS_PER_SAMPLE) {
        Some(Some(v)) => if v.len() >= 1 { Some(v) } else { None },
        Some(None) => Some(seq![1nat]),
        None => None,
    };
    let (has_bits, same, b0): (bool, bool, u32) = match field_exec(b, le, o, n, 258) {
        Ok(Some(f)) => if f.count >= 1 {
            (true, same_exec(b, le, f), value_exec(b, le, f, 0))
        } else {
            (false, true, 0)
        },
        Ok(None) => {
            assert(all_same(seq![1nat]));
            (true, true, 1)
        },
        Err(()) => (false, true, 0),
    };
    assert(has_bits == bv is Some);
    assert(has_bits ==> same == all_same(bv->Some_0) && b0 as nat == bv->Some_0[0]);
    let c1 = match comp {
        Some(c) => c == 2 || c == 3 || c == 4 || c == 6 || c == 7,
        None => false,
    };
    let c2 = first_exec(b, le, o, n, 262) == Some(6u32);
    let c3 = first_exec(b, le, o, n, 266) == Some(2u32);
    let c4 = has_bits && (!same || b0 > 32);
    let c5 = match field_exec(b, le, o, n, 339) {
        Ok(Some(f)) => f.count >= 1 && !same_exec(b, le, f),
        _ => false,
    };
    let c6 = match comp {
        Some(c) => (c == 5 || c == 8) && (pred == Some(3u32) || (pred == Some(2u32) && has_bits
            && !(b0 == 8 || b0 == 16 || b0 == 32))),
        None => false,
    };
    c1 || c2 || c3 || c4 || c5 || c6
}

/// `spec::unsupported`.
fn unsupported_exec(b: &[u8]) -> (r: bool)
    ensures
        r == unsupported(b@),
{
    if bigtiff_exec(b) {
        return true;
    }
    match header_exec(b) {
        None => false,
        Some((le, o)) => {
            if o as u64 + 2 > b.len() as u64 {
                return false;
            }
            let n = u16_exec(b, le, o as usize) as usize;
            if n == 0 || o as u64 + 2 + 12 * n as u64 > b.len() as u64 {
                false
            } else {
                unsupported_ifd_exec(b, le, o as usize, n)
            }
        },
    }
}

/// Decodes the first image of a TIFF file. The output, and each strip or
/// tile while it is decoded, may take at most `limit` bytes.
///
/// The result is the specification's: `Ok` exactly with the spec's image,
/// `Unsupported` exactly for the TIFF files `spec::unsupported` names, and
/// `Invalid` for the other files the spec rejects. `TooLarge` and
/// `OutOfMemory` are the only other results.
pub fn decode(b: &[u8], limit: usize) -> (r: Result<Tiff, Error>)
    ensures
        match r {
            Ok(t) => spec::decode(b@) == Some(t.view()),
            Err(Error::Invalid) => spec::decode(b@) is None && !spec::unsupported(b@),
            Err(Error::Unsupported) => spec::decode(b@) is None && spec::unsupported(b@),
            Err(_) => !spec::unsupported(b@),
        },
{
    if unsupported_exec(b) {
        return Err(Error::Unsupported);
    }
    let (le, o) = match header_exec(b) {
        Some(x) => x,
        None => return Err(Error::Invalid),
    };
    let p = match params_exec(b, le, o) {
        Some(p) => p,
        None => return Err(Error::Invalid),
    };
    let ghost pv = p.view(b@);
    let rb = row_bytes_exec(&p, Ghost(b@));
    if rb > limit as u128 {
        return Err(Error::TooLarge);
    }
    proof {
        lemma_mul_inequality(p.height as int, u32::MAX as int, rb as int);
        lemma_mul_inequality(rb as int, 0xffff_ffff_ffff_ffff, u32::MAX as int);
        lemma_mul_is_commutative(p.height as int, rb as int);
    }
    let ps = p.height as u128 * rb;
    if ps > limit as u128 {
        return Err(Error::TooLarge);
    }
    let planes: u128 = if p.planar == 2 { p.spp as u128 } else { 1 };
    proof {
        lemma_mul_inequality(planes as int, u32::MAX as int, ps as int);
        lemma_mul_inequality(ps as int, 0xffff_ffff_ffff_ffff, u32::MAX as int);
        lemma_mul_is_commutative(planes as int, ps as int);
    }
    let size = planes * ps;
    if size > limit as u128 {
        return Err(Error::TooLarge);
    }
    let mut out = match alloc_zeroed(size as usize) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut off = match alloc_u32(4096) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let mut len = match alloc_u32(4096) {
        Some(v) => v,
        None => return Err(Error::OutOfMemory),
    };
    let n = p.offsets.count;
    let mut k: u32 = 0;
    proof {
        assert forall|i: int|
            0 <= i < pv.image_size() && #[trigger] owner(pv, i).0 < 0 implies out@[i] == chunk(b@, pv, owner(pv, i).0 as nat)->Some_0[owner(pv, i).1] by {
            if pv.tiled {
                lemma_tile_b(pv, i);
            } else {
                lemma_strip_b(pv, i);
            }
        }
    }
    while k < n
        invariant
            !spec::unsupported(b@),
            pv == p.view(b@),
            pv.wf(),
            p.ok(b@),
            spec::header(b@) == Some((le, o as nat)),
            params(b@, le, o as nat) == Some(pv),
            n as nat == pv.chunks(),
            p.counts.count == n,
            out@.len() == pv.image_size(),
            pv.image_size() <= u64::MAX,
            off@.len() == STORED,
            len@.len() == STORED,
            k <= n,
            forall|j: nat| j < k ==> #[trigger] chunk(b@, pv, j) is Some,
            placed(b@, pv, out@, k as int),
        decreases n - k,
    {
        let v = match chunk_exec(b, &p, k, limit, off.as_mut_slice(), len.as_mut_slice()) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if e == Error::Invalid {
                        assert(k < pv.chunks() && chunk(b@, pv, k as nat) is None);
                    }
                }
                return Err(e);
            },
        };
        if p.tiled {
            place_tile(out.as_mut_slice(), v.as_slice(), &p, k, Ghost(b@));
        } else {
            place_strip(out.as_mut_slice(), v.as_slice(), &p, k, Ghost(b@));
        }
        k = k + 1;
    }
    let t = Tiff {
        le,
        width: p.width,
        height: p.height,
        bits_per_sample: p.bps,
        samples_per_pixel: p.spp,
        compression: p.compression,
        photometric: p.photometric,
        sample_format: p.sample_format,
        planar: p.planar,
        pixels: out,
    };
    proof {
        let cs = Seq::new(pv.chunks(), |j: int| chunk(b@, pv, j as nat)->Some_0);
        assert(!exists|j: nat| j < pv.chunks() && chunk(b@, pv, j) is None);
        assert forall|i: int| 0 <= i < pv.image_size() implies #[trigger] t.pixels@[i] == pixel(pv, cs, i) by {
            if pv.tiled {
                lemma_tile_b(pv, i);
            } else {
                lemma_strip_b(pv, i);
            }
        }
        assert(t.pixels@ =~= Seq::new(pv.image_size(), |i: int| pixel(pv, cs, i)));
    }
    Ok(t)
}

} // verus!
