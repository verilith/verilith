//! A PNG encoder for 8-bit RGBA images, proven to round-trip: for every
//! image, what `encode_rgba` writes decodes, under verilith-png's
//! specification of PNG decoding (`verilith_png::spec::decode`), to
//! exactly that image. The rows are filtered (each with whichever of the
//! five filters makes the smallest sum of signed bytes, libpng's
//! heuristic) and compressed with verilith-zlib's verified compressor.
use verilith_png::spec as P;
use vstd::prelude::*;
#[cfg(verus_only)]
use verilith_zlib::spec as Z;

verus! {

// ---------------------------------------------------------------------------
// Bytes and chunks
// ---------------------------------------------------------------------------

/// `v` as four bytes, most significant first.
pub open spec fn be4(v: nat) -> Seq<u8> {
    seq![(v / 16777216) as u8, ((v / 65536) % 256) as u8, ((v / 256) % 256) as u8, (v % 256) as u8]
}

/// A chunk of type `ty` with data `d`: length, type, data, CRC.
pub open spec fn chunk_bytes(ty: Seq<u8>, d: Seq<u8>) -> Seq<u8> {
    be4(d.len()) + ty + d + be4(Z::crc32(ty + d) as nat)
}

fn be_bytes(a: u32) -> (r: [u8; 4])
    ensures
        r@ == be4(a as nat),
{
    let b0 = (a >> 24) as u8;
    let b1 = (a >> 16) as u8;
    let b2 = (a >> 8) as u8;
    let b3 = a as u8;
    assert(b0 == (a / 16777216) as u8 && b1 == ((a / 65536) % 256) as u8 && b2 == ((a / 256) % 256) as u8 && b3
        == (a % 256) as u8) by (bit_vector)
        requires
            b0 == (a >> 24) as u8,
            b1 == (a >> 16) as u8,
            b2 == (a >> 8) as u8,
            b3 == a as u8,
    ;
    let r = [b0, b1, b2, b3];
    assert(r@ =~= be4(a as nat));
    r
}

proof fn lemma_be4(v: nat, b: Seq<u8>, p: int)
    requires
        v < 0x1_0000_0000,
        0 <= p,
        p + 4 <= b.len(),
        b.subrange(p, p + 4) == be4(v),
    ensures
        P::be32(b, p) == v,
{
    assert(b[p] == be4(v)[0] && b[p + 1] == be4(v)[1] && b[p + 2] == be4(v)[2] && b[p + 3] == be4(v)[3]);
    let a = v as u32;
    assert(((((a / 16777216) as u8) as nat * 256 + ((a / 65536) % 256) as u8 as nat) * 256 + ((a / 256)
        % 256) as u8 as nat) * 256 + (a % 256) as u8 as nat == a as nat) by (bit_vector);
}

/// Appends a chunk.
fn put_chunk(out: &mut Vec<u8>, ty: [u8; 4], d: &[u8])
    requires
        d@.len() <= P::MAX_LEN,
    ensures
        final(out)@ == old(out)@ + chunk_bytes(ty@, d@),
{
    let lb = be_bytes(d.len() as u32);
    verilith_core::prims::extend(out, &lb);
    let start = out.len();
    verilith_core::prims::extend(out, &ty);
    verilith_core::prims::extend(out, d);
    let end = out.len();
    let crc = verilith_checksum::crc32(vstd::slice::slice_subrange(out.as_slice(), start, end));
    let cb = be_bytes(crc);
    proof {
        assert(out@.subrange(start as int, end as int) =~= ty@ + d@);
    }
    verilith_core::prims::extend(out, &cb);
    proof {
        assert(final(out)@ =~= old(out)@ + chunk_bytes(ty@, d@));
    }
}

/// `c` sits at `p` in `b`, byte by byte.
proof fn lemma_sub_at(b: Seq<u8>, p: int, c: Seq<u8>)
    requires
        0 <= p,
        p + c.len() <= b.len(),
        b.subrange(p, p + c.len()) == c,
    ensures
        forall|j: int| 0 <= j < c.len() ==> b[p + j] == #[trigger] c[j],
{
    assert forall|j: int| 0 <= j < c.len() implies b[p + j] == #[trigger] c[j] by {
        assert(b.subrange(p, p + c.len())[j] == b[p + j]);
    }
}

/// What `chunk_at` reads from a chunk written by `put_chunk`.
proof fn lemma_chunk_at(b: Seq<u8>, p: int, ty: Seq<u8>, d: Seq<u8>)
    requires
        0 <= p,
        ty.len() == 4,
        d.len() <= P::MAX_LEN,
        p + 12 + d.len() <= b.len(),
        b.subrange(p, p + 12 + d.len()) == chunk_bytes(ty, d),
        P::is_letter(ty[0]) && P::is_letter(ty[1]) && 65 <= ty[2] <= 90 && P::is_letter(ty[3]),
    ensures
        P::chunk_at(b, p) == Some(P::Chunk { len: d.len(), ty: P::be32(ty, 0), crc_ok: true }),
        P::chunk_data(b, p, d.len()) == d,
{
    let n = d.len() as int;
    let l4 = be4(d.len());
    let c4 = be4(Z::crc32(ty + d) as nat);
    let c = chunk_bytes(ty, d);
    assert(c.len() == 12 + n);
    lemma_sub_at(b, p, c);
    assert forall|j: int| 0 <= j < 4 implies b[p + j] == #[trigger] l4[j] by {
        assert(c[j] == l4[j]);
    }
    assert forall|j: int| 0 <= j < 4 implies b[p + 4 + j] == #[trigger] ty[j] by {
        assert(c[4 + j] == ty[j]);
    }
    assert forall|j: int| 0 <= j < n implies b[p + 8 + j] == #[trigger] d[j] by {
        assert(c[8 + j] == d[j]);
    }
    assert forall|j: int| 0 <= j < 4 implies b[p + 8 + n + j] == #[trigger] c4[j] by {
        assert(c[8 + n + j] == c4[j]);
    }
    assert(b.subrange(p, p + 4) =~= l4);
    lemma_be4(d.len(), b, p);
    assert(b.subrange(p + 4, p + 8) =~= ty);
    assert(b[p + 4] == ty[0] && b[p + 5] == ty[1] && b[p + 6] == ty[2] && b[p + 7] == ty[3]);
    assert(b.subrange(p + 4, p + 8 + n) =~= ty + d);
    assert(b.subrange(p + 8 + n, p + 12 + n) =~= c4);
    lemma_be4(Z::crc32(ty + d) as nat, b, p + 8 + n);
    assert(P::be32(b, p + 4) == P::be32(ty, 0));
    assert(P::chunk_data(b, p, d.len()) =~= d);
}

// ---------------------------------------------------------------------------
// Filters
// ---------------------------------------------------------------------------

/// The bytes to the left of byte `i` of a row (`bpp` bytes per pixel): 0
/// before the row starts.
pub open spec fn left(r: Seq<u8>, i: int, bpp: nat) -> u8 {
    if i >= bpp { r[i - bpp] } else { 0u8 }
}

/// `cur` is the row `orig` (below `prev`) filtered with filter `ft`: each
/// byte plus its predictor is the original byte.
pub open spec fn filtered(ft: u8, prev: Seq<u8>, orig: Seq<u8>, cur: Seq<u8>, bpp: nat, n: nat) -> bool {
    forall|i: int|
        0 <= i < n ==> ((#[trigger] cur[i] as nat + P::predict(ft, left(orig, i, bpp), prev[i], left(prev, i, bpp))
            as nat) % 256) as u8 == orig[i]
}

/// Reconstructing a filtered row gives back the original.
proof fn lemma_recon(ft: u8, prev: Seq<u8>, orig: Seq<u8>, cur: Seq<u8>, bpp: nat, n: nat)
    requires
        bpp >= 1,
        n <= orig.len(),
        n <= prev.len(),
        n <= cur.len(),
        filtered(ft, prev, orig, cur, bpp, n),
    ensures
        P::recon(ft, prev, cur, bpp, n) == orig.subrange(0, n as int),
    decreases n,
{
    if n > 0 {
        let m = (n - 1) as nat;
        let i = m as int;
        lemma_recon(ft, prev, orig, cur, bpp, m);
        let r = P::recon(ft, prev, cur, bpp, m);
        assert(r == orig.subrange(0, i));
        let a = if i >= bpp { r[i - bpp] } else { 0u8 };
        let c = if i >= bpp { prev[i - bpp] } else { 0u8 };
        assert(a == left(orig, i, bpp));
        assert(c == left(prev, i, bpp));
        assert(((cur[i] as nat + P::predict(ft, left(orig, i, bpp), prev[i], left(prev, i, bpp)) as nat) % 256) as u8
            == orig[i]);
        assert(P::recon(ft, prev, cur, bpp, n) == r.push(((cur[i] as nat + P::predict(ft, a, prev[i], c) as nat) % 256) as u8));
        assert(orig.subrange(0, n as int) =~= orig.subrange(0, i).push(orig[i]));
    } else {
        assert(orig.subrange(0, 0) =~= Seq::<u8>::empty());
    }
}

/// The image's rows (each `rb` bytes of `px`) filtered into `raw`: a
/// filter byte (0 to 4) and the filtered row, for each of the first `n`.
pub open spec fn rows_filtered(px: Seq<u8>, raw: Seq<u8>, rb: nat, bpp: nat, n: nat) -> bool {
    &&& raw.len() >= n * (rb + 1)
    &&& px.len() >= n * rb
    &&& forall|r: int|
        0 <= r < n ==> {
            let i = #[trigger] (r * (rb + 1));
            &&& raw[i] <= 4
            &&& filtered(
                raw[i],
                if r == 0 { P::zeros(rb) } else { px.subrange((r - 1) * rb, r * rb) },
                px.subrange(r * rb, (r + 1) * rb),
                raw.subrange(i + 1, i + 1 + rb),
                bpp,
                rb,
            )
        }
}

proof fn lemma_recon_rows(px: Seq<u8>, raw: Seq<u8>, rb: nat, bpp: nat, n: nat)
    requires
        bpp >= 1,
        rows_filtered(px, raw, rb, bpp, n),
    ensures
        P::recon_rows(raw, 0, rb, bpp, n) == Some(px.subrange(0, (n * rb) as int)),
    decreases n,
{
    if n == 0 {
        assert(px.subrange(0, 0) =~= Seq::<u8>::empty());
    } else {
        let m = (n - 1) as nat;
        let mi = m as int;
        let rbi = rb as int;
        assert(m * (rb + 1) <= n * (rb + 1)) by (nonlinear_arith)
            requires
                m <= n,
        ;
        assert(m * rb <= n * rb) by (nonlinear_arith)
            requires
                m <= n,
        ;
        lemma_recon_rows(px, raw, rb, bpp, m);
        let done = px.subrange(0, (m * rb) as int);
        let i = mi * (rbi + 1);
        assert(n * rb == m * rb + rb) by (nonlinear_arith)
            requires
                m == n - 1,
        ;
        assert(n * (rb + 1) == m * (rb + 1) + rb + 1) by (nonlinear_arith)
            requires
                m == n - 1,
        ;
        assert(i == (m as int) * (rb + 1));
        let prev = if n == 1 { P::zeros(rb) } else { done.subrange((n - 2) * rb, (n - 1) * rb) };
        let sprev = if m == 0 { P::zeros(rb) } else { px.subrange(((m - 1) * rb) as int, (m * rb) as int) };
        if n != 1 {
            assert((n - 1) * rb == m * rb);
            assert((n - 2) * rb == (m - 1) * rb);
            assert(0 <= (m - 1) * rb) by (nonlinear_arith)
                requires
                    m >= 1,
            ;
            assert((n - 1) * rb - (n - 2) * rb == rb) by (nonlinear_arith);
            assert((m - 1) * rb <= m * rb) by (nonlinear_arith)
                requires
                    m >= 1,
            ;
            assert(prev =~= sprev);
        }
        let orig = px.subrange(mi * rbi, (mi + 1) * rbi);
        let cur = raw.subrange(i + 1, i + 1 + rbi);
        assert(filtered(raw[i], sprev, orig, cur, bpp, rb));
        lemma_recon(raw[i], prev, orig, cur, bpp, rb);
        assert(orig.subrange(0, rb as int) =~= orig);
        assert(done + orig =~= px.subrange(0, (n * rb) as int));
    }
}

/// `spec::paeth`.
fn paeth_x(a: u8, b: u8, c: u8) -> (r: u8)
    ensures
        r == P::paeth(a, b, c),
{
    let p = a as i32 + b as i32 - c as i32;
    let pa = if p >= a as i32 { p - a as i32 } else { a as i32 - p };
    let pb = if p >= b as i32 { p - b as i32 } else { b as i32 - p };
    let pc = if p >= c as i32 { p - c as i32 } else { c as i32 - p };
    if pa <= pb && pa <= pc {
        a
    } else if pb <= pc {
        b
    } else {
        c
    }
}

/// `spec::predict`.
#[inline(always)]
fn predict_x(ft: u8, a: u8, b: u8, c: u8) -> (r: u8)
    ensures
        r == P::predict(ft, a, b, c),
{
    if ft == 1 {
        a
    } else if ft == 2 {
        b
    } else if ft == 3 {
        ((a as u16 + b as u16) / 2) as u8
    } else if ft == 4 {
        paeth_x(a, b, c)
    } else {
        0
    }
}

/// The filtered byte that, plus predictor `p`, gives `o`.
#[inline(always)]
fn sub_x(o: u8, p: u8) -> (r: u8)
    ensures
        ((r as nat + p as nat) % 256) as u8 == o,
{
    let r = ((o as u16 + 256 - p as u16) % 256) as u8;
    assert(((((o as u16 + 256 - p as u16) % 256) as u8 as nat + p as nat) % 256) as u8 == o) by (bit_vector);
    r
}

/// Byte `i` of row `r` filtered with `ft`; `r` is the row at `px[off..]`,
/// the one above at `px[off - rb..]` (zeros when `off == 0`).
#[inline(always)]
fn filt_byte(px: &[u8], off: usize, rb: usize, i: usize, ft: u8) -> (r: u8)
    requires
        off + rb <= px@.len(),
        i < rb,
        off == 0 || off >= rb,
    ensures
        ({
            let prev = if off == 0 { P::zeros(rb as nat) } else { px@.subrange(off - rb, off as int) };
            let orig = px@.subrange(off as int, off + rb);
            ((r as nat + P::predict(ft, left(orig, i as int, 4), prev[i as int], left(prev, i as int, 4)) as nat)
                % 256) as u8 == orig[i as int]
        }),
{
    let a = if i >= 4 { px[off + i - 4] } else { 0 };
    let b = if off > 0 { px[off - rb + i] } else { 0 };
    let c = if off > 0 && i >= 4 { px[off - rb + i - 4] } else { 0 };
    sub_x(px[off + i], predict_x(ft, a, b, c))
}

/// The cost of filter `ft` on a row: the sum of the filtered bytes as
/// signed numbers' magnitudes. Not part of the theorem: any choice
/// round-trips.
fn cost(px: &[u8], off: usize, rb: usize, ft: u8) -> (r: u64)
    requires
        off + rb <= px@.len(),
        off == 0 || off >= rb,
        rb <= 0x1_0000_0000,
{
    let mut s: u64 = 0;
    let mut i: usize = 0;
    while i < rb
        invariant
            off + rb <= px@.len(),
            off == 0 || off >= rb,
            rb <= 0x1_0000_0000,
            i <= rb,
            s <= i * 128,
        decreases rb - i,
    {
        let v = filt_byte(px, off, rb, i, ft);
        s = s + if v < 128 { v as u64 } else { 256 - v as u64 };
        i = i + 1;
    }
    s
}

/// Appends row `off / rb` filtered with `ft`, after its filter byte.
fn put_row(raw: &mut Vec<u8>, px: &[u8], off: usize, rb: usize, ft: u8)
    requires
        off + rb <= px@.len(),
        off == 0 || off >= rb,
        ft <= 4,
        old(raw)@.len() + rb + 1 <= usize::MAX,
    ensures
        final(raw)@.len() == old(raw)@.len() + rb + 1,
        final(raw)@.subrange(0, old(raw)@.len() as int) == old(raw)@,
        final(raw)@[old(raw)@.len() as int] == ft,
        filtered(
            ft,
            if off == 0 { P::zeros(rb as nat) } else { px@.subrange(off - rb, off as int) },
            px@.subrange(off as int, off + rb),
            final(raw)@.subrange((old(raw)@.len() + 1) as int, (old(raw)@.len() + 1 + rb) as int),
            4,
            rb as nat,
        ),
{
    let ghost start = raw@.len();
    raw.push(ft);
    let mut i: usize = 0;
    while i < rb
        invariant
            off + rb <= px@.len(),
            off == 0 || off >= rb,
            start + rb + 1 <= usize::MAX,
            i <= rb,
            raw@.len() == start + 1 + i,
            raw@.subrange(0, start as int) == old(raw)@,
            raw@[start as int] == ft,
            forall|j: int|
                0 <= j < i ==> {
                    let prev = if off == 0 { P::zeros(rb as nat) } else { px@.subrange(off - rb, off as int) };
                    let orig = px@.subrange(off as int, off + rb);
                    ((#[trigger] raw@[start + 1 + j] as nat + P::predict(ft, left(orig, j, 4), prev[j], left(prev, j, 4))
                        as nat) % 256) as u8 == orig[j]
                },
        decreases rb - i,
    {
        let v = filt_byte(px, off, rb, i, ft);
        let ghost before = raw@;
        raw.push(v);
        proof {
            assert(raw@.subrange(0, start as int) =~= before.subrange(0, start as int));
        }
        i = i + 1;
    }
    proof {
        let cur = raw@.subrange((start + 1) as int, (start + 1 + rb) as int);
        assert forall|j: int| 0 <= j < rb implies cur[j] == raw@[start + 1 + j] by {}
    }
}

/// The filtered image data: each row with the filter that costs least.
fn filter_rows(px: &[u8], rb: usize, h: usize) -> (r: Vec<u8>)
    requires
        1 <= rb <= 0x1_0000_0000,
        px@.len() == rb * h,
        (rb + 1) * h <= usize::MAX,
    ensures
        r@.len() == (rb + 1) * h,
        rows_filtered(px@, r@, rb as nat, 4, h as nat),
{
    let mut raw: Vec<u8> = Vec::with_capacity((rb + 1) * h);
    let mut y: usize = 0;
    while y < h
        invariant
            1 <= rb <= 0x1_0000_0000,
            px@.len() == rb * h,
            (rb + 1) * h <= usize::MAX,
            y <= h,
            raw@.len() == y * (rb + 1),
            rows_filtered(px@, raw@, rb as nat, 4, y as nat),
        decreases h - y,
    {
        proof {
            assert(y * rb + rb <= rb * h) by (nonlinear_arith)
                requires
                    y < h,
            ;
            assert(y * (rb + 1) + rb + 1 <= (rb + 1) * h) by (nonlinear_arith)
                requires
                    y < h,
            ;
            assert(rb * h <= (rb + 1) * h) by (nonlinear_arith);
            assert(y == 0 || y * rb >= rb) by (nonlinear_arith)
                requires
                    rb >= 1,
            ;
        }
        let off = y * rb;
        let mut best: u8 = 0;
        let mut bc = cost(px, off, rb, 0);
        let mut ft: u8 = 1;
        while ft <= 4
            invariant
                off + rb <= px@.len(),
                off == 0 || off >= rb,
                rb <= 0x1_0000_0000,
                1 <= ft <= 5,
                best <= 4,
            decreases 5 - ft,
        {
            let c = cost(px, off, rb, ft);
            if c < bc {
                bc = c;
                best = ft;
            }
            ft = ft + 1;
        }
        let ghost before = raw@;
        put_row(&mut raw, px, off, rb, best);
        proof {
            let n = (y + 1) as nat;
            assert((y + 1) * (rb + 1) == y * (rb + 1) + rb + 1) by (nonlinear_arith);
            assert(y * (rb + 1) == before.len());
            assert((y + 1) * rb == y * rb + rb) by (nonlinear_arith);
            assert(px@.len() >= n * rb) by (nonlinear_arith)
                requires
                    px@.len() == rb * h,
                    n <= h,
            ;
            assert forall|r: int| 0 <= r < n implies {
                let i = #[trigger] (r * (rb + 1));
                &&& raw@[i] <= 4
                &&& filtered(
                    raw@[i],
                    if r == 0 { P::zeros(rb as nat) } else { px@.subrange((r - 1) * rb, r * rb) },
                    px@.subrange(r * rb, (r + 1) * rb),
                    raw@.subrange(i + 1, i + 1 + rb),
                    4,
                    rb as nat,
                )
            } by {
                let i = r * (rb + 1);
                if r < y {
                    assert(i + 1 + rb <= before.len()) by (nonlinear_arith)
                        requires
                            r < y,
                            i == r * (rb + 1),
                            before.len() == y * (rb + 1),
                    ;
                    assert(raw@[i] == before[i]);
                    assert(raw@.subrange(i + 1, i + 1 + rb) =~= before.subrange(i + 1, i + 1 + rb));
                } else {
                    assert(r == y);
                    assert((r + 1) * rb == r * rb + rb) by (nonlinear_arith);
                    if r != 0 {
                        assert((r - 1) * rb == r * rb - rb) by (nonlinear_arith);
                    }
                }
            }
        }
        y = y + 1;
    }
    proof {
        assert(h * (rb + 1) == (rb + 1) * h) by (nonlinear_arith);
    }
    raw
}

// ---------------------------------------------------------------------------
// The file
// ---------------------------------------------------------------------------

/// The header `encode_rgba` writes.
pub open spec fn rgba_ihdr(w: nat, h: nat) -> P::Ihdr {
    P::Ihdr { w, h, depth: 8, ct: 6, interlace: 0 }
}

proof fn lemma_rgba8(png: P::Png, imgs: Seq<Seq<u8>>, px: Seq<u8>)
    requires
        png.hdr == rgba_ihdr(png.hdr.w, png.hdr.h),
        png.hdr.w >= 1,
        imgs.len() == 1,
        imgs[0] == px,
        px.len() == png.hdr.w * png.hdr.h * 4,
    ensures
        P::rgba8(png, imgs) == px,
{
    let h = png.hdr;
    let w = h.w as int;
    assert(4 * h.w * h.h == px.len()) by (nonlinear_arith)
        requires
            px.len() == h.w * h.h * 4,
    ;
    assert(P::row_bytes(h, P::pass_w(h, 0)) == 4 * w) by {
        assert(P::pass_w(h, 0) == h.w);
        assert((h.w * 32 + 7) / 8 == 4 * h.w) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((h.w * 32 + 7) as int, 8, 4 * w, 7);
        }
    }
    assert forall|k: int| 0 <= k < px.len() implies #[trigger] P::rgba8(png, imgs)[k] == px[k] by {
        let q = k / 4;
        let j = k % 4;
        let x = q % w;
        let y = q / w;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(k, 4);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q, w);
        vstd::arithmetic::div_mod::lemma_mod_bound(k, 4);
        vstd::arithmetic::div_mod::lemma_mod_bound(q, w);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(k, 4);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(q, w);
        assert(((x * 4 + j) * 8) / 8 == x * 4 + j) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((x * 4 + j) * 8, 8, x * 4 + j, 0);
        }
        assert(y * (4 * w) + (x * 4 + j) == k) by (nonlinear_arith)
            requires
                k == 4 * q + j,
                q == w * y + x,
        ;
        assert(P::channels(6) == 4);
        assert(P::pass_of(h, x as nat, y as nat) == 0);
        assert(P::dx(h, 0) == 1 && P::dy(h, 0) == 1);
        assert((x as nat) / 1 == x as nat && (y as nat) / 1 == y as nat);
        assert(P::sample(h, imgs[0], (4 * w) as nat, x as nat, y as nat, j as nat) == px[k] as nat);
    }
    assert(P::rgba8(png, imgs) =~= px);
}

/// The chunk types this encoder writes.
pub open spec fn t_ihdr() -> Seq<u8> { seq![73u8, 72, 68, 82] }
pub open spec fn t_idat() -> Seq<u8> { seq![73u8, 68, 65, 84] }
pub open spec fn t_iend() -> Seq<u8> { seq![73u8, 69, 78, 68] }

/// IHDR data for an RGBA image, 8 bits, not interlaced.
pub open spec fn ihdr_data(w: nat, h: nat) -> Seq<u8> {
    be4(w) + be4(h) + seq![8u8, 6, 0, 0, 0]
}

/// The file `encode_rgba` writes around compressed image data `z`.
pub open spec fn file(w: nat, h: nat, z: Seq<u8>) -> Seq<u8> {
    P::signature() + chunk_bytes(t_ihdr(), ihdr_data(w, h)) + chunk_bytes(t_idat(), z) + chunk_bytes(
        t_iend(),
        Seq::empty(),
    )
}

proof fn lemma_layout(w: nat, h: nat, z: Seq<u8>)
    ensures
        file(w, h, z).len() == 57 + z.len(),
        file(w, h, z).subrange(0, 8) == P::signature(),
        file(w, h, z).subrange(8, 33) == chunk_bytes(t_ihdr(), ihdr_data(w, h)),
        file(w, h, z).subrange(33, 45 + z.len() as int) == chunk_bytes(t_idat(), z),
        file(w, h, z).subrange(45 + z.len() as int, 57 + z.len() as int) == chunk_bytes(t_iend(), Seq::empty()),
{
    let s = P::signature();
    let a = chunk_bytes(t_ihdr(), ihdr_data(w, h));
    let i = chunk_bytes(t_idat(), z);
    let e = chunk_bytes(t_iend(), Seq::empty());
    let b = file(w, h, z);
    assert(b == s + a + i + e);
    assert(s.len() == 8 && a.len() == 25 && i.len() == 12 + z.len() && e.len() == 12);
    assert(b.subrange(0, 8) =~= s);
    assert(b.subrange(8, 33) =~= a);
    assert(b.subrange(33, 45 + z.len() as int) =~= i);
    assert(b.subrange(45 + z.len() as int, 57 + z.len() as int) =~= e);
}

proof fn lemma_ihdr(w: nat, h: nat)
    requires
        1 <= w <= P::MAX_LEN,
        1 <= h <= P::MAX_LEN,
    ensures
        P::parse_ihdr(ihdr_data(w, h)) == Some(rgba_ihdr(w, h)),
{
    let d = ihdr_data(w, h);
    assert(d.subrange(0, 4) =~= be4(w));
    assert(d.subrange(4, 8) =~= be4(h));
    lemma_be4(w, d, 0);
    lemma_be4(h, d, 4);
}

proof fn lemma_walk(b: Seq<u8>, hd: P::Ihdr, z: Seq<u8>)
    requires
        hd.ct == 6,
        b.len() == 57 + z.len(),
        P::chunk_at(b, 33) == Some(P::Chunk { len: z.len(), ty: P::IDAT, crc_ok: true }),
        P::chunk_data(b, 33, z.len()) == z,
        P::chunk_at(b, 45 + z.len() as int) == Some(P::Chunk { len: 0, ty: P::IEND, crc_ok: true }),
    ensures
        P::walk(b, hd, 33, P::walk_start()) == Some(P::Walk { idat: z, phase: 1, ..P::walk_start() }),
{
    let zl = z.len() as int;
    let st1 = P::Walk { idat: z, phase: 1, ..P::walk_start() };
    assert(P::step(b, hd, 33, P::Chunk { len: zl as nat, ty: P::IDAT, crc_ok: true }, P::walk_start()) == Ok::<
        P::Walk,
        bool,
    >(st1));
    assert(P::step(b, hd, 45 + zl, P::Chunk { len: 0, ty: P::IEND, crc_ok: true }, st1) == Err::<P::Walk, bool>(
        true,
    ));
    reveal_with_fuel(P::walk, 2);
    assert(P::walk(b, hd, 45 + zl, st1) == Some(st1));
}

#[verifier::spinoff_prover]
proof fn lemma_container(w: nat, h: nat, z: Seq<u8>)
    requires
        1 <= w <= P::MAX_LEN,
        1 <= h <= P::MAX_LEN,
        z.len() <= P::MAX_LEN,
    ensures
        P::container(file(w, h, z)) == Some((rgba_ihdr(w, h), P::Walk { idat: z, phase: 1, ..P::walk_start() })),
{
    let b = file(w, h, z);
    let zl = z.len() as int;
    lemma_layout(w, h, z);
    lemma_chunk_at(b, 8, t_ihdr(), ihdr_data(w, h));
    lemma_chunk_at(b, 33, t_idat(), z);
    lemma_chunk_at(b, 45 + zl, t_iend(), Seq::empty());
    assert(P::be32(t_ihdr(), 0) == P::IHDR);
    assert(P::be32(t_idat(), 0) == P::IDAT);
    assert(P::be32(t_iend(), 0) == P::IEND);
    lemma_ihdr(w, h);
    lemma_walk(b, rgba_ihdr(w, h), z);
    reveal(P::container);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
proof fn lemma_decode(w: nat, h: nat, z: Seq<u8>, raw: Seq<u8>, px: Seq<u8>)
    requires
        1 <= w <= 0x4000_0000,
        1 <= h <= P::MAX_LEN,
        z.len() <= P::MAX_LEN,
        Z::zlib_decompress(z) == Some((raw, z.len() as int)),
        raw.len() == (4 * w + 1) * h,
        px.len() == w * h * 4,
        rows_filtered(px, raw, 4 * w, 4, h),
    ensures
        P::decode(file(w, h, z), P::Format::Rgba8) == Some((rgba_ihdr(w, h), px)),
{
    let b = file(w, h, z);
    let hd = rgba_ihdr(w, h);
    let rb = 4 * w;
    lemma_container(w, h, z);
    assert(P::pass_w(hd, 0) == w);
    assert(P::pass_h(hd, 0) == h);
    assert(P::row_bytes(hd, w) == rb) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((w * 32 + 7) as int, 8, rb as int, 7);
    }
    assert(P::pass_size(hd, 0) == h * (1 + rb));
    assert(P::raw_size(hd) == P::pass_size(hd, 0));
    assert(raw.len() == P::raw_size(hd)) by (nonlinear_arith)
        requires
            raw.len() == (rb + 1) * h,
            P::raw_size(hd) == h * (1 + rb),
    ;
    reveal(P::zlib);
    assert(raw.subrange(0, P::raw_size(hd) as int) =~= raw);
    reveal(P::parse);
    let png = P::Png { hdr: hd, plte: Seq::empty(), trns: None, raw };
    assert(P::parse(b) == Some(png));
    assert(P::filter_bpp(hd) == 4);
    assert(P::pass_off(hd, 0) == 0);
    lemma_recon_rows(px, raw, rb, 4, h);
    assert(h * rb == px.len()) by (nonlinear_arith)
        requires
            px.len() == w * h * 4,
            rb == 4 * w,
    ;
    assert(px.subrange(0, (h * rb) as int) =~= px);
    assert(P::pass_size(hd, 0) > 0) by (nonlinear_arith)
        requires
            P::pass_size(hd, 0) == h * (1 + rb),
            h >= 1,
    ;
    assert(P::pass_image(hd, raw, 0) == Some(px));
    reveal_with_fuel(P::pass_images, 2);
    let imgs = seq![px];
    assert(P::pass_images(hd, raw, 0) == Some(Seq::<Seq<u8>>::empty()));
    assert(Seq::<Seq<u8>>::empty().push(px) =~= imgs);
    assert(P::pass_images(hd, raw, 1) == Some(imgs));
    assert(P::npasses(hd) == 1);
    lemma_rgba8(png, imgs, px);
}

/// Encodes an RGBA image (`w` by `h` pixels, 4 bytes each, row by row) as
/// a PNG file: RGBA, 8 bits, not interlaced, compressed at zlib `level`.
/// `None` only when the compressed image data does not fit in one chunk
/// (2^31 - 1 bytes).
///
/// Theorem: the file decodes, under verilith-png's specification, to
/// exactly this header and these pixels.
pub fn encode_rgba(px: &[u8], w: u32, h: u32, level: u32) -> (r: Option<Vec<u8>>)
    requires
        1 <= w <= 0x4000_0000,
        1 <= h <= P::MAX_LEN,
        px@.len() == w * h * 4,
        (4 * w + 1) * h <= usize::MAX,
    ensures
        r matches Some(b) ==> P::decode(b@, P::Format::Rgba8) == Some((rgba_ihdr(w as nat, h as nat), px@)),
{
    let rb = 4 * w as usize;
    proof {
        assert(px@.len() == rb * h) by (nonlinear_arith)
            requires
                px@.len() == w * h * 4,
                rb == 4 * w,
        ;
    }
    let raw = filter_rows(px, rb, h as usize);
    let z = verilith_zlib::deflate::zlib_compress(&raw, level);
    if z.len() > 0x7fff_ffff {
        return None;
    }
    let mut out: Vec<u8> = Vec::with_capacity(z.len() + 57);
    let sig: [u8; 8] = [137, 80, 78, 71, 13, 10, 26, 10];
    verilith_core::prims::extend(&mut out, &sig);
    let wb = be_bytes(w);
    let hb = be_bytes(h);
    let ihdr: [u8; 13] = [wb[0], wb[1], wb[2], wb[3], hb[0], hb[1], hb[2], hb[3], 8, 6, 0, 0, 0];
    put_chunk(&mut out, [73, 72, 68, 82], &ihdr);
    put_chunk(&mut out, [73, 68, 65, 84], &z);
    let empty: [u8; 0] = [];
    put_chunk(&mut out, [73, 69, 78, 68], &empty);
    proof {
        assert(ihdr@ =~= ihdr_data(w as nat, h as nat));
        assert(empty@ =~= Seq::<u8>::empty());
        assert([73u8, 72, 68, 82]@ =~= t_ihdr());
        assert([73u8, 68, 65, 84]@ =~= t_idat());
        assert([73u8, 69, 78, 68]@ =~= t_iend());
        assert(sig@ =~= P::signature());
        assert(out@ =~= file(w as nat, h as nat, z@));
        assert(raw@.len() == (4 * w + 1) * h);
        lemma_decode(w as nat, h as nat, z@, raw@, px@);
    }
    Some(out)
}

} // verus!
