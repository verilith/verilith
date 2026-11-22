//! The frame decoder, proven equal to `spec::frames`: headers, blocks
//! (linked or independent, compressed or stored), block and content
//! checksums, content sizes, skippable frames, and frames one after
//! another.
use crate::block::decode_block;
#[cfg(verus_only)]
use crate::block::lemma_seqs_len;
use crate::spec::*;
use verilith_core::lz::load32;
#[cfg(verus_only)]
use verilith_core::prims::le_bytes;
use verilith_core::prims::{copy_in, get, load_u64_le};
use verilith_xxhash::xxh32_exec;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The spec's `le` is vcore's `le_bytes`.
pub proof fn lemma_le_is(b: Seq<u8>, i: int, n: nat)
    ensures
        le(b, i, n) == le_bytes(b, i, n),
    decreases n,
{
    if n > 0 {
        lemma_le_is(b, i + 1, (n - 1) as nat);
    }
}

/// The four bytes at `i`, little-endian.
#[inline(always)]
pub fn word(b: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= b@.len(),
    ensures
        r == le32(b@, i as int),
        r == le(b@, i as int, 4),
{
    let r = load32(b, i);
    proof {
        lemma_le_is(b@, i as int, 4);
    }
    r
}

/// Why decompression failed.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    /// The input is not what the format allows.
    Corrupt,
    /// The output would be longer than the limit given.
    TooLarge,
}

/// No output is longer than this, whatever limit is asked for.
pub const MAX_OUT: usize = 0x4000_0000_0000_0000;

/// A frame header, as `spec::Header`.
#[derive(Debug, Clone, Copy)]
pub struct Hdr {
    pub indep: bool,
    pub bsum: bool,
    pub csize: Option<u64>,
    pub csum: bool,
    pub dict: Option<u32>,
    pub bmax: usize,
    pub end: usize,
}

impl Hdr {
    pub open spec fn view(&self) -> Header {
        Header {
            indep: self.indep,
            bsum: self.bsum,
            csize: match self.csize {
                Some(c) => Some(c as nat),
                None => None,
            },
            csum: self.csum,
            dict: match self.dict {
                Some(c) => Some(c as nat),
                None => None,
            },
            bmax: self.bmax as nat,
            end: self.end as int,
        }
    }
}

/// The frame header at `i` (`spec::header`).
pub fn read_header(src: &[u8], i: usize) -> (r: Option<Hdr>)
    requires
        i <= src@.len(),
    ensures
        match r {
            Some(h) => header(src@, i as int) == Some(h@) && i + 7 <= h.end <= src@.len() && 0x1_0000 <= h.bmax
                <= 0x40_0000,
            None => header(src@, i as int).is_none(),
        },
{
    let n = src.len();
    if n - i < 7 {
        return None;
    }
    if word(src, i) != 0x184D2204 {
        return None;
    }
    let flg = get(src, i + 4);
    let bd = get(src, i + 5);
    let has_size = (flg / 8) % 2 == 1;
    let has_dict = flg % 2 == 1;
    let dlen: usize = 2 + (if has_size {
        8
    } else {
        0
    }) + (if has_dict {
        4
    } else {
        0
    });
    if flg / 64 != 1 || (flg / 2) % 2 != 0 || bd / 128 != 0 || bd % 16 != 0 || (bd / 16) % 8 < 4 {
        return None;
    }
    if n - i < 4 + dlen + 1 {
        return None;
    }
    let x = xxh32_exec(slice_subrange(src, i + 4, i + 4 + dlen));
    if get(src, i + 4 + dlen) as u32 != (x / 256) % 256 {
        return None;
    }
    let csize = if has_size {
        let v = load_u64_le(src, i + 6);
        proof {
            lemma_le_is(src@, i + 6, 8);
        }
        Some(v)
    } else {
        None
    };
    let dict = if has_dict {
        Some(word(src, i + 4 + dlen - 4))
    } else {
        None
    };
    let code = (bd / 16) % 8;
    let bmax: usize = if code == 4 {
        0x1_0000
    } else if code == 5 {
        0x4_0000
    } else if code == 6 {
        0x10_0000
    } else {
        0x40_0000
    };
    Some(
        Hdr {
            indep: (flg / 32) % 2 == 1,
            bsum: (flg / 16) % 2 == 1,
            csize,
            csum: (flg / 4) % 2 == 1,
            dict,
            bmax,
            end: i + 4 + dlen + 1,
        },
    )
}

/// The content only grows from block to block.
pub proof fn lemma_blocks_len(s: Seq<u8>, i: int, h: Header, d: Seq<u8>, out: Seq<u8>)
    ensures
        blocks(s, i, h, d, out) matches Some((o, j)) ==> o.len() >= out.len() && i < j <= s.len(),
    decreases s.len() - i,
{
    if 0 <= i && i + 4 <= s.len() {
        let w = le(s, i, 4);
        let size = w % 0x8000_0000;
        let raw = w >= 0x8000_0000;
        let j = i + 4;
        let e = j + size + (if h.bsum {
            4int
        } else {
            0
        });
        if size != 0 && size <= h.bmax && e <= s.len() {
            let data = s.subrange(j, j + size);
            let r = block_data(data, raw, h.indep, d, out);
            lemma_block_data_len(data, raw, h.indep, d, out);
            match r {
                None => {},
                Some(out2) => {
                    lemma_blocks_len(s, e, h, d, out2);
                },
            }
        }
    }
}

/// A block's data only adds to the content.
pub proof fn lemma_block_data_len(data: Seq<u8>, raw: bool, indep: bool, d: Seq<u8>, out: Seq<u8>)
    ensures
        block_data(data, raw, indep, d, out) matches Some(o) ==> o.len() >= out.len(),
{
    lemma_seqs_len(data, 0, d, None);
    lemma_seqs_len(data, 0, d + out, None);
}

/// With no dictionary, a block is decoded after the earlier content
/// (linked) or on its own (independent).
pub proof fn lemma_block_data_nodict(data: Seq<u8>, raw: bool, indep: bool, out: Seq<u8>)
    ensures
        block_data(data, raw, indep, Seq::empty(), out) == if raw {
            Some(out + data)
        } else if indep {
            match block(data, Seq::empty()) {
                Some(b) => Some(out + b),
                None => None,
            }
        } else {
            block(data, out)
        },
{
    assert(Seq::<u8>::empty() + out =~= out);
    if let Some(b) = block(data, Seq::empty()) {
        assert(b.subrange(0, b.len() as int) =~= b);
    }
    if let Some(b) = block(data, out) {
        assert(b.subrange(0, b.len() as int) =~= b);
    }
}

/// An independent block decoded after the dictionary `dict`, which is
/// `scratch[..dl]`: it is decoded there, then copied to `out` at `op`.
fn decode_indep(
    data: &[u8],
    bmax: usize,
    out: &mut Vec<u8>,
    base: usize,
    op: usize,
    scratch: &mut Vec<u8>,
    dl: usize,
    Ghost(dict): Ghost<Seq<u8>>,
) -> (r: Result<usize, ()>)
    requires
        base <= op <= old(out)@.len(),
        op <= MAX_OUT,
        0 < dl <= 0x1_0000,
        bmax <= 0x40_0000,
        dl <= old(scratch)@.len(),
        dict.len() == dl,
        old(scratch)@.subrange(0, dl as int) == dict,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, op as int) == old(out)@.subrange(0, op as int),
        dl <= final(scratch)@.len(),
        final(scratch)@.subrange(0, dl as int) == dict,
        match r {
            Ok(op2) => op <= op2 <= final(out)@.len() && op2 - op <= bmax && block_data(
                data@,
                false,
                true,
                dict,
                old(out)@.subrange(base as int, op as int),
            ) == Some(final(out)@.subrange(base as int, op2 as int)),
            Err(_) => match block_data(data@, false, true, dict, old(out)@.subrange(base as int, op as int)) {
                Some(o) => o.len() - (op - base) > bmax,
                None => true,
            },
        },
{
    let ghost before = out@;
    let ghost cur = out@.subrange(base as int, op as int);
    let ghost s0 = scratch@;
    if scratch.len() < dl + bmax {
        scratch.resize(dl + bmax, 0);
    }
    proof {
        assert(scratch@.subrange(0, dl as int) =~= s0.subrange(0, dl as int));
        lemma_seqs_len(data@, 0, dict, None);
    }
    let r = decode_block(data, scratch.as_mut_slice(), 0, dl);
    match r {
        None => Err(()),
        Some(e) => {
            let m = e - dl;
            if m > bmax {
                return Err(());
            }
            if out.len() < op + m {
                out.resize(op + m, 0);
            }
            let ghost mid = out@;
            copy_in(out.as_mut_slice(), op, scratch.as_slice(), dl, m);
            proof {
                let b = scratch@.subrange(0, e as int);
                assert(b.subrange(dl as int, b.len() as int) =~= scratch@.subrange(dl as int, e as int));
                assert(mid.subrange(0, op as int) =~= before.subrange(0, op as int));
                assert(out@.subrange(base as int, op + m) =~= cur + scratch@.subrange(dl as int, e as int));
                assert(out@.subrange(0, op as int) =~= before.subrange(0, op as int));
            }
            Ok(op + m)
        },
    }
}

/// One block's data, `src[j..j + size]`, decoded or copied to `out` at
/// `op` (`spec::block_data`). The frame's content starts at `base`, and
/// the dictionary is `out[hb..base]` (empty when `hb == base`); `scratch`
/// starts with a copy of it, for independent blocks, which need it right
/// before their own output. `out` is lengthened if it has to be. Gives the
/// content's new end.
fn decode_one(
    src: &[u8],
    j: usize,
    size: usize,
    raw: bool,
    indep: bool,
    bmax: usize,
    out: &mut Vec<u8>,
    hb: usize,
    base: usize,
    op: usize,
    scratch: &mut Vec<u8>,
) -> (r: Result<usize, ()>)
    requires
        j + size <= src@.len(),
        hb <= base <= op <= old(out)@.len(),
        op <= MAX_OUT,
        base - hb <= 0x1_0000,
        0 < size <= bmax <= 0x40_0000,
        base - hb <= old(scratch)@.len(),
        old(scratch)@.subrange(0, base - hb) == old(out)@.subrange(hb as int, base as int),
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, base as int) == old(out)@.subrange(0, base as int),
        base - hb <= final(scratch)@.len(),
        final(scratch)@.subrange(0, base - hb) == old(scratch)@.subrange(0, base - hb),
        match r {
            Ok(op2) => op <= op2 <= final(out)@.len() && op2 - op <= bmax && block_data(
                src@.subrange(j as int, j + size),
                raw,
                indep,
                old(out)@.subrange(hb as int, base as int),
                old(out)@.subrange(base as int, op as int),
            ) == Some(final(out)@.subrange(base as int, op2 as int)),
            Err(_) => match block_data(
                src@.subrange(j as int, j + size),
                raw,
                indep,
                old(out)@.subrange(hb as int, base as int),
                old(out)@.subrange(base as int, op as int),
            ) {
                Some(o) => o.len() - (op - base) > bmax,
                None => true,
            },
        },
{
    let ghost before = out@;
    let ghost cur = out@.subrange(base as int, op as int);
    let ghost dict = out@.subrange(hb as int, base as int);
    let n = src.len();
    let dl = base - hb;
    let data = slice_subrange(src, j, j + size);
    if raw {
        if out.len() < op + size {
            out.resize(op + size, 0);
        }
        let ghost mid = out@;
        copy_in(out.as_mut_slice(), op, src, j, size);
        proof {
            assert(mid.subrange(0, op as int) =~= before.subrange(0, op as int));
            assert(out@.subrange(base as int, op + size) =~= cur + data@);
            assert(out@.subrange(0, base as int) =~= before.subrange(0, base as int));
        }
        Ok(op + size)
    } else if indep && dl > 0 {
        let ghost b4 = out@;
        let r = decode_indep(data, bmax, out, base, op, scratch, dl, Ghost(dict));
        proof {
            assert(out@.subrange(0, base as int) =~= out@.subrange(0, op as int).subrange(0, base as int));
            assert(b4.subrange(0, base as int) =~= b4.subrange(0, op as int).subrange(0, base as int));
        }
        r
    } else {
        if out.len() < op + bmax {
            out.resize(op + bmax, 0);
        }
        let ghost mid = out@;
        let lo = if indep {
            op
        } else {
            hb
        };
        proof {
            assert(mid.subrange(0, op as int) =~= before.subrange(0, op as int));
            assert(mid.subrange(lo as int, op as int) =~= before.subrange(lo as int, op as int));
            if indep {
                assert(mid.subrange(lo as int, op as int) =~= Seq::<u8>::empty());
                assert(dict =~= Seq::<u8>::empty());
            } else {
                assert(mid.subrange(lo as int, op as int) =~= dict + cur);
            }
            lemma_seqs_len(data@, 0, mid.subrange(lo as int, op as int), None);
        }
        match decode_block(data, out.as_mut_slice(), lo, op) {
            None => Err(()),
            Some(op2) => {
                proof {
                    assert(out@.subrange(0, base as int) =~= out@.subrange(0, op as int).subrange(0, base as int));
                    assert(mid.subrange(0, base as int) =~= mid.subrange(0, op as int).subrange(0, base as int));
                    assert(mid.subrange(0, base as int) =~= before.subrange(0, base as int));
                    let b = out@.subrange(lo as int, op2 as int);
                    if indep {
                        assert forall|x: int| base <= x < op implies out@[x] == mid[x] by {
                            assert(out@.subrange(0, op as int)[x] == mid.subrange(0, op as int)[x]);
                        }
                        assert(b.subrange(0, b.len() as int) =~= b);
                        assert(out@.subrange(base as int, op2 as int) =~= cur + b);
                    } else {
                        assert(b.subrange(dl as int, b.len() as int) =~= out@.subrange(base as int, op2 as int));
                    }
                }
                if op2 - op > bmax {
                    Err(())
                } else {
                    Ok(op2)
                }
            },
        }
    }
}

/// Decodes the blocks of a frame from `i`, appending the content to
/// `out`, up to the end mark (`spec::blocks`), with the dictionary
/// `out[hb..]` (`scratch` starts with a copy of it). Gives the index after
/// the end mark. `out` may be longer than `limit` by one block before
/// `TooLarge` is returned; on an error it is left with its old contents
/// and some of the frame's.
fn decode_blocks(
    src: &[u8],
    i0: usize,
    h: &Hdr,
    out: &mut Vec<u8>,
    hb: usize,
    scratch: &mut Vec<u8>,
    limit: usize,
) -> (r: Result<usize, Error>)
    requires
        i0 <= src@.len(),
        0x1_0000 <= h.bmax <= 0x40_0000,
        limit <= MAX_OUT,
        old(out)@.len() <= limit,
        hb <= old(out)@.len(),
        old(out)@.len() - hb <= 0x1_0000,
        old(out)@.len() - hb <= old(scratch)@.len(),
        old(scratch)@.subrange(0, old(out)@.len() - hb) == old(out)@.subrange(hb as int, old(out)@.len() as int),
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        match r {
            Ok(j) => blocks(
                src@,
                i0 as int,
                h@,
                old(out)@.subrange(hb as int, old(out)@.len() as int),
                Seq::empty(),
            ) == Some((final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), j as int)) && i0 < j
                <= src@.len() && final(out)@.len() <= limit,
            Err(Error::Corrupt) => blocks(
                src@,
                i0 as int,
                h@,
                old(out)@.subrange(hb as int, old(out)@.len() as int),
                Seq::empty(),
            ).is_none(),
            Err(Error::TooLarge) => blocks(
                src@,
                i0 as int,
                h@,
                old(out)@.subrange(hb as int, old(out)@.len() as int),
                Seq::empty(),
            ) matches Some((c, _j)) ==> old(out)@.len() + c.len() > limit,
        },
{
    let n = src.len();
    let base = out.len();
    let bmax = h.bmax;
    let ghost dict = out@.subrange(hb as int, base as int);
    let ghost goal = blocks(src@, i0 as int, h@, dict, Seq::empty());
    let mut i = i0;
    // The content so far is `out[base..op]`; `out` is kept longer, so that
    // a block always has room to decode into.
    let mut op = base;
    proof {
        assert(out@.subrange(base as int, op as int) =~= Seq::empty());
        assert(out@.subrange(0, base as int) =~= old(out)@);
    }
    loop
        invariant
            n == src@.len(),
            i0 <= i <= n,
            base == old(out)@.len(),
            hb <= base <= op <= out@.len(),
            base - hb <= 0x1_0000,
            base - hb <= scratch@.len(),
            scratch@.subrange(0, base - hb) == dict,
            dict == old(out)@.subrange(hb as int, base as int),
            op <= limit,
            limit <= MAX_OUT,
            bmax == h.bmax,
            0x1_0000 <= bmax <= 0x40_0000,
            goal == blocks(src@, i0 as int, h@, dict, Seq::empty()),
            blocks(src@, i as int, h@, dict, out@.subrange(base as int, op as int)) == goal,
            out@.subrange(0, base as int) == old(out)@,
        decreases n - i,
    {
        if n - i < 4 {
            return Err(Error::Corrupt);
        }
        let ghost cur = out@.subrange(base as int, op as int);
        let w = word(src, i) as usize;
        let size = w & 0x7fff_ffff;
        let raw = w >= 0x8000_0000;
        proof {
            assert(w & 0x7fff_ffff == w % 0x8000_0000) by (bit_vector);
        }
        let j = i + 4;
        if size == 0 {
            let ghost before = out@;
            out.truncate(op);
            proof {
                assert(out@.subrange(base as int, op as int) =~= cur);
                assert(out@.subrange(0, base as int) =~= before.subrange(0, base as int));
                lemma_blocks_len(src@, i0 as int, h@, dict, Seq::empty());
            }
            return Ok(j);
        }
        let extra: usize = if h.bsum {
            4
        } else {
            0
        };
        if size > bmax || size + extra > n - j {
            return Err(Error::Corrupt);
        }
        let data = slice_subrange(src, j, j + size);
        if h.bsum {
            if word(src, j + size) != xxh32_exec(data) {
                return Err(Error::Corrupt);
            }
        }
        let e = j + size + extra;
        proof {
            assert(out@.subrange(hb as int, base as int) =~= out@.subrange(0, base as int).subrange(
                hb as int,
                base as int,
            ));
            assert(old(out)@.subrange(hb as int, base as int) =~= old(out)@.subrange(0, base as int).subrange(
                hb as int,
                base as int,
            ));
        }
        let op2 = match decode_one(src, j, size, raw, h.indep, bmax, out, hb, base, op, scratch) {
            Err(_) => {
                return Err(Error::Corrupt);
            },
            Ok(m) => m,
        };
        if op2 > limit {
            proof {
                lemma_blocks_len(src@, e as int, h@, dict, out@.subrange(base as int, op2 as int));
            }
            return Err(Error::TooLarge);
        }
        i = e;
        op = op2;
    }
}

/// Decodes the frame at `i`, appending its content to `out`, with the
/// dictionary `out[hb..]`, the window of `d` (`spec::frame_dict`).
fn decode_frame_in(
    src: &[u8],
    i: usize,
    out: &mut Vec<u8>,
    hb: usize,
    scratch: &mut Vec<u8>,
    limit: usize,
    Ghost(d): Ghost<Seq<u8>>,
) -> (r: Result<usize, Error>)
    requires
        i <= src@.len(),
        limit <= MAX_OUT,
        old(out)@.len() <= limit,
        hb <= old(out)@.len(),
        old(out)@.len() - hb <= 0x1_0000,
        old(out)@.len() - hb <= old(scratch)@.len(),
        old(scratch)@.subrange(0, old(out)@.len() - hb) == old(out)@.subrange(hb as int, old(out)@.len() as int),
        dict_window(d) == old(out)@.subrange(hb as int, old(out)@.len() as int),
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        match r {
            Ok(j) => frame_dict(src@, i as int, d) == Some(
                (final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), j as int),
            ) && i < j <= src@.len() && final(out)@.len() <= limit,
            Err(Error::Corrupt) => frame_dict(src@, i as int, d).is_none(),
            Err(Error::TooLarge) => frame_dict(src@, i as int, d) matches Some((c, _j)) ==> old(out)@.len() + c.len()
                > limit,
        },
{
    let n = src.len();
    let base = out.len();
    let h = match read_header(src, i) {
        None => {
            return Err(Error::Corrupt);
        },
        Some(h) => h,
    };
    let j = match decode_blocks(src, h.end, &h, out, hb, scratch, limit) {
        Err(e) => {
            return Err(e);
        },
        Ok(j) => j,
    };
    match h.csize {
        Some(c) => {
            if c != (out.len() - base) as u64 {
                return Err(Error::Corrupt);
            }
        },
        None => {},
    }
    if h.csum {
        if n - j < 4 {
            return Err(Error::Corrupt);
        }
        let x = xxh32_exec(slice_subrange(out.as_slice(), base, out.len()));
        if word(src, j) != x {
            return Err(Error::Corrupt);
        }
        Ok(j + 4)
    } else {
        Ok(j)
    }
}

/// Decodes the frame at `i`, appending its content to `out`
/// (`spec::frame`). Gives the index after the frame. On an error `out`
/// is left with its old contents and some of the frame's.
pub fn decode_frame(src: &[u8], i: usize, out: &mut Vec<u8>, limit: usize) -> (r: Result<usize, Error>)
    requires
        i <= src@.len(),
        limit <= MAX_OUT,
        old(out)@.len() <= limit,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        match r {
            Ok(j) => frame(src@, i as int) == Some(
                (final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), j as int),
            ) && i < j <= src@.len() && final(out)@.len() <= limit,
            Err(Error::Corrupt) => frame(src@, i as int).is_none(),
            Err(Error::TooLarge) => frame(src@, i as int) matches Some((c, _j)) ==> old(out)@.len() + c.len() > limit,
        },
{
    let base = out.len();
    let mut scratch: Vec<u8> = Vec::new();
    proof {
        assert(scratch@.subrange(0, 0) =~= out@.subrange(base as int, base as int));
        assert(dict_window(Seq::empty()) =~= out@.subrange(base as int, base as int));
    }
    decode_frame_in(src, i, out, base, &mut scratch, limit, Ghost(Seq::empty()))
}

/// The most a frame decoded with a dictionary may produce: room is kept
/// below `MAX_OUT` for the dictionary's window.
pub const MAX_DICT_OUT: usize = MAX_OUT - 0x1_0000;

/// Decodes the frame at `i` with the dictionary `dict`, appending its
/// content to `out` (`spec::frame_dict`), as `LZ4F_decompress_usingDict`
/// does. Only the last 64 KiB of `dict` are used. Gives the index after
/// the frame. On an error `out` is left as it was, or, with an empty
/// dictionary, as `decode_frame` leaves it.
pub fn decode_frame_dict(src: &[u8], i: usize, dict: &[u8], out: &mut Vec<u8>, limit: usize) -> (r: Result<
    usize,
    Error,
>)
    requires
        i <= src@.len(),
        limit <= MAX_DICT_OUT,
        old(out)@.len() <= limit,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        match r {
            Ok(j) => frame_dict(src@, i as int, dict@) == Some(
                (final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), j as int),
            ) && i < j <= src@.len() && final(out)@.len() <= limit,
            Err(Error::Corrupt) => frame_dict(src@, i as int, dict@).is_none(),
            Err(Error::TooLarge) => frame_dict(src@, i as int, dict@) matches Some((c, _j)) ==> old(out)@.len()
                + c.len() > limit,
        },
{
    let dn = dict.len();
    if dn == 0 {
        proof {
            assert(dict@ =~= Seq::<u8>::empty());
        }
        return decode_frame(src, i, out, limit);
    }
    let dl = if dn > 0x1_0000 {
        0x1_0000
    } else {
        dn
    };
    let ds = dn - dl;
    // The window, then the content after it.
    let mut w: Vec<u8> = Vec::new();
    w.resize(dl, 0);
    copy_in(w.as_mut_slice(), 0, dict, ds, dl);
    let mut scratch: Vec<u8> = Vec::new();
    scratch.resize(dl, 0);
    copy_in(scratch.as_mut_slice(), 0, dict, ds, dl);
    let room = limit - out.len();
    proof {
        assert(w@ =~= dict@.subrange(ds as int, dn as int));
        assert(scratch@ =~= dict@.subrange(ds as int, dn as int));
        assert(dict_window(dict@) =~= w@.subrange(0, dl as int));
        assert(scratch@.subrange(0, dl as int) =~= w@.subrange(0, dl as int));
    }
    let ghost w0 = w@;
    let r = decode_frame_in(src, i, &mut w, 0, &mut scratch, dl + room, Ghost(dict@));
    match r {
        Err(e) => Err(e),
        Ok(j) => {
            let m = w.len() - dl;
            let ol = out.len();
            let ghost before = out@;
            out.resize(ol + m, 0);
            let ghost mid = out@;
            copy_in(out.as_mut_slice(), ol, w.as_slice(), dl, m);
            proof {
                assert(mid.subrange(0, ol as int) =~= before);
                assert(out@.subrange(0, ol as int) =~= before);
                assert(out@.subrange(ol as int, out@.len() as int) =~= w@.subrange(dl as int, w@.len() as int));
            }
            Ok(j)
        },
    }
}

// ---------------------------------------------------------------------------
// Into a buffer that already exists
// ---------------------------------------------------------------------------

/// As `decode_one`, into a slice: `None` if the block is not valid or
/// there is no room for it.
fn decode_one_into(
    src: &[u8],
    j: usize,
    size: usize,
    raw: bool,
    indep: bool,
    bmax: usize,
    out: &mut [u8],
    base: usize,
    op: usize,
) -> (r: Option<usize>)
    requires
        j + size <= src@.len(),
        base <= op <= old(out)@.len(),
        0 < size <= bmax <= 0x40_0000,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, base as int) == old(out)@.subrange(0, base as int),
        r matches Some(op2) ==> op <= op2 <= final(out)@.len() && op2 - op <= bmax && block_data(
            src@.subrange(j as int, j + size),
            raw,
            indep,
            Seq::empty(),
            old(out)@.subrange(base as int, op as int),
        ) == Some(final(out)@.subrange(base as int, op2 as int)),
{
    let ghost before = out@;
    let ghost cur = out@.subrange(base as int, op as int);
    proof {
        lemma_block_data_nodict(src@.subrange(j as int, j + size), raw, indep, cur);
    }
    let len = out.len();
    let n = src.len();
    let data = slice_subrange(src, j, j + size);
    if raw {
        if size > len - op {
            return None;
        }
        copy_in(out, op, src, j, size);
        proof {
            assert(out@.subrange(base as int, op + size) =~= cur + data@);
            assert(out@.subrange(0, base as int) =~= before.subrange(0, base as int));
        }
        Some(op + size)
    } else {
        let lo = if indep {
            op
        } else {
            base
        };
        proof {
            if indep {
                assert(before.subrange(lo as int, op as int) =~= Seq::<u8>::empty());
            }
        }
        match decode_block(data, out, lo, op) {
            None => None,
            Some(op2) => {
                proof {
                    assert(out@.subrange(0, base as int) =~= out@.subrange(0, op as int).subrange(0, base as int));
                    assert(before.subrange(0, base as int) =~= before.subrange(0, op as int).subrange(0, base as int));
                    if indep {
                        let b = out@.subrange(op as int, op2 as int);
                        assert forall|x: int| base <= x < op implies out@[x] == before[x] by {
                            assert(out@.subrange(0, op as int)[x] == before.subrange(0, op as int)[x]);
                        }
                        assert(out@.subrange(base as int, op2 as int) =~= cur + b);
                    }
                }
                if op2 - op > bmax {
                    None
                } else {
                    Some(op2)
                }
            },
        }
    }
}

/// Decodes the frame at `i` into `out` from `base` (`spec::frame`), for
/// callers that already have the buffer the content goes to. Nothing is
/// allocated, and nothing before `base` is touched.
///
/// `Some((j, end))`: the frame is valid, ends at `j`, and its content is
/// `out[base..end]`. `None`: the frame is not valid, or its content does
/// not fit; `decode_frame` says which.
pub fn decode_frame_into(src: &[u8], i: usize, out: &mut [u8], base: usize) -> (r: Option<(usize, usize)>)
    requires
        i <= src@.len(),
        base <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, base as int) == old(out)@.subrange(0, base as int),
        r matches Some((j, end)) ==> base <= end <= final(out)@.len() && i < j <= src@.len() && frame(src@, i as int)
            == Some((final(out)@.subrange(base as int, end as int), j as int)),
{
    let n = src.len();
    let h = match read_header(src, i) {
        None => {
            return None;
        },
        Some(h) => h,
    };
    let bmax = h.bmax;
    let ghost goal = blocks(src@, h.end as int, h@, Seq::empty(), Seq::empty());
    proof {
        assert(dict_window(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
    }
    let mut k = h.end;
    let mut op = base;
    proof {
        assert(out@.subrange(base as int, op as int) =~= Seq::empty());
    }
    let mut j: usize = 0;
    let mut done = false;
    while !done
        invariant
            n == src@.len(),
            i < h.end <= k <= n,
            out@.len() == old(out)@.len(),
            base <= op <= out@.len(),
            bmax == h.bmax,
            0x1_0000 <= bmax <= 0x40_0000,
            goal == blocks(src@, h.end as int, h@, Seq::empty(), Seq::empty()),
            !done ==> blocks(src@, k as int, h@, Seq::empty(), out@.subrange(base as int, op as int)) == goal,
            done ==> h.end < j <= n && goal == Some((out@.subrange(base as int, op as int), j as int)),
            out@.subrange(0, base as int) == old(out)@.subrange(0, base as int),
        decreases (if done { 0int } else { 1int }), n - k,
    {
        if n - k < 4 {
            return None;
        }
        let w = word(src, k) as usize;
        let size = w & 0x7fff_ffff;
        let raw = w >= 0x8000_0000;
        proof {
            assert(w & 0x7fff_ffff == w % 0x8000_0000) by (bit_vector);
        }
        let j2 = k + 4;
        if size == 0 {
            j = j2;
            done = true;
        } else {
            let extra: usize = if h.bsum {
                4
            } else {
                0
            };
            if size > bmax || size + extra > n - j2 {
                return None;
            }
            let data = slice_subrange(src, j2, j2 + size);
            if h.bsum {
                if word(src, j2 + size) != xxh32_exec(data) {
                    return None;
                }
            }
            let op2 = match decode_one_into(src, j2, size, raw, h.indep, bmax, out, base, op) {
                None => {
                    return None;
                },
                Some(m) => m,
            };
            k = j2 + size + extra;
            op = op2;
        }
    }
    match h.csize {
        Some(c) => {
            if c != (op - base) as u64 {
                return None;
            }
        },
        None => {},
    }
    if h.csum {
        if n - j < 4 {
            return None;
        }
        let x = xxh32_exec(slice_subrange(out, base, op));
        if word(src, j) != x {
            return None;
        }
        Some((j + 4, op))
    } else {
        Some((j, op))
    }
}

/// `a` before what `r` holds.
pub open spec fn prepend(a: Seq<u8>, r: Option<Seq<u8>>) -> Option<Seq<u8>> {
    match r {
        Some(b) => Some(a + b),
        None => None,
    }
}

/// Decompresses `src`: one or more frames, and any skippable frames
/// between them (`spec::frames`). Empty input gives empty output.
///
/// - `Ok(v)`: `src` is valid and `v` is its content.
/// - `Err(Corrupt)`: `src` is not valid.
/// - `Err(TooLarge)`: `src` is not valid, or its content is longer than
///   `limit` (or `MAX_OUT`). At most `limit` plus one block (4 MiB) of
///   memory is used for output before this is returned.
pub fn decompress(src: &[u8], limit: usize) -> (r: Result<Vec<u8>, Error>)
    ensures
        match r {
            Ok(v) => frames(src@, 0) == Some(v@) && v@.len() <= limit,
            Err(Error::Corrupt) => frames(src@, 0).is_none(),
            Err(Error::TooLarge) => frames(src@, 0) matches Some(c) ==> c.len() > limit || c.len() > MAX_OUT,
        },
{
    let n = src.len();
    let lim = if limit > MAX_OUT {
        MAX_OUT
    } else {
        limit
    };
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(prepend(out@, frames(src@, 0)) =~= frames(src@, 0)) by {
            if frames(src@, 0).is_some() {
                assert(out@ + frames(src@, 0).unwrap() =~= frames(src@, 0).unwrap());
            }
        }
    }
    while i < n
        invariant
            n == src@.len(),
            i <= n,
            lim <= MAX_OUT,
            lim <= limit,
            limit > MAX_OUT ==> lim == MAX_OUT,
            limit <= MAX_OUT ==> lim == limit,
            out@.len() <= lim,
            frames(src@, 0) == prepend(out@, frames(src@, i as int)),
        decreases n - i,
    {
        if n - i >= 8 && word(src, i) / 16 == 0x184D2A5 {
            let size = word(src, i + 4) as usize;
            if size > n - i - 8 {
                return Err(Error::Corrupt);
            }
            i = i + 8 + size;
        } else {
            let ghost before = out@;
            match decode_frame(src, i, &mut out, lim) {
                Err(Error::Corrupt) => {
                    return Err(Error::Corrupt);
                },
                Err(Error::TooLarge) => {
                    proof {
                        if frames(src@, 0).is_some() {
                            let (c, j) = frame(src@, i as int).unwrap();
                            let r = frames(src@, j).unwrap();
                            assert(frames(src@, 0).unwrap() == before + (c + r));
                        }
                    }
                    return Err(Error::TooLarge);
                },
                Ok(j) => {
                    proof {
                        let c = out@.subrange(before.len() as int, out@.len() as int);
                        assert(out@ =~= before + c);
                        if frames(src@, j as int).is_some() {
                            let r = frames(src@, j as int).unwrap();
                            assert(before + (c + r) =~= out@ + r);
                        }
                    }
                    i = j;
                },
            }
        }
    }
    proof {
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    Ok(out)
}

} // verus!
