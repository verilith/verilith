//! The frame decoder, proven equal to `spec::frames`: headers, blocks
//! (linked or independent, compressed or stored), block and content
//! checksums, content sizes, skippable frames, and frames one after
//! another.
use crate::block::decode_block;
#[cfg(verus_only)]
use crate::block::lemma_seqs_len;
use crate::spec::*;
#[cfg(verus_only)]
use crate::xxh::lemma_le_is;
use crate::xxh::{word, xxh32_exec};
use verilith_core::prims::{copy_in, get, load_u64_le};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

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
pub proof fn lemma_blocks_len(s: Seq<u8>, i: int, h: Header, out: Seq<u8>)
    ensures
        blocks(s, i, h, out) matches Some((o, j)) ==> o.len() >= out.len() && i < j <= s.len(),
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
            let r = block_data(data, raw, h.indep, out);
            lemma_seqs_len(data, 0, out, None);
            match r {
                None => {},
                Some(out2) => {
                    lemma_blocks_len(s, e, h, out2);
                },
            }
        }
    }
}

/// One block's data, `src[j..j + size]`, decoded or copied to `out` at
/// `op` (`spec::block_data`); the frame's content starts at `base`. `out`
/// is lengthened if it has to be. Gives the content's new end.
fn decode_one(
    src: &[u8],
    j: usize,
    size: usize,
    raw: bool,
    indep: bool,
    bmax: usize,
    out: &mut Vec<u8>,
    base: usize,
    op: usize,
) -> (r: Result<usize, ()>)
    requires
        j + size <= src@.len(),
        base <= op <= old(out)@.len(),
        op <= MAX_OUT,
        0 < size <= bmax <= 0x40_0000,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, base as int) == old(out)@.subrange(0, base as int),
        match r {
            Ok(op2) => op <= op2 <= final(out)@.len() && op2 - op <= bmax && block_data(
                src@.subrange(j as int, j + size),
                raw,
                indep,
                old(out)@.subrange(base as int, op as int),
            ) == Some(final(out)@.subrange(base as int, op2 as int)),
            Err(_) => match block_data(
                src@.subrange(j as int, j + size),
                raw,
                indep,
                old(out)@.subrange(base as int, op as int),
            ) {
                Some(o) => o.len() - (op - base) > bmax,
                None => true,
            },
        },
{
    let ghost before = out@;
    let ghost cur = out@.subrange(base as int, op as int);
    let n = src.len();
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
    } else {
        if out.len() < op + bmax {
            out.resize(op + bmax, 0);
        }
        let ghost mid = out@;
        let lo = if indep {
            op
        } else {
            base
        };
        proof {
            assert(mid.subrange(0, op as int) =~= before.subrange(0, op as int));
            assert(mid.subrange(lo as int, op as int) =~= before.subrange(lo as int, op as int));
            if indep {
                assert(mid.subrange(lo as int, op as int) =~= Seq::<u8>::empty());
            }
        }
        match decode_block(data, out.as_mut_slice(), lo, op) {
            None => Err(()),
            Some(op2) => {
                proof {
                    assert(out@.subrange(0, base as int) =~= out@.subrange(0, op as int).subrange(0, base as int));
                    assert(mid.subrange(0, base as int) =~= mid.subrange(0, op as int).subrange(0, base as int));
                    assert(mid.subrange(0, base as int) =~= before.subrange(0, base as int));
                    if indep {
                        let b = out@.subrange(op as int, op2 as int);
                        assert forall|x: int| base <= x < op implies out@[x] == mid[x] by {
                            assert(out@.subrange(0, op as int)[x] == mid.subrange(0, op as int)[x]);
                        }
                        assert(out@.subrange(base as int, op2 as int) =~= cur + b);
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
/// `out`, up to the end mark (`spec::blocks`). Gives the index after the
/// end mark. `out` may be longer than `limit` by one block before
/// `TooLarge` is returned; on an error it is left with its old contents
/// and some of the frame's.
fn decode_blocks(src: &[u8], i0: usize, h: &Hdr, out: &mut Vec<u8>, limit: usize) -> (r: Result<usize, Error>)
    requires
        i0 <= src@.len(),
        0x1_0000 <= h.bmax <= 0x40_0000,
        limit <= MAX_OUT,
        old(out)@.len() <= limit,
    ensures
        final(out)@.len() >= old(out)@.len(),
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        match r {
            Ok(j) => blocks(src@, i0 as int, h@, Seq::empty()) == Some(
                (final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int), j as int),
            ) && i0 < j <= src@.len() && final(out)@.len() <= limit,
            Err(Error::Corrupt) => blocks(src@, i0 as int, h@, Seq::empty()).is_none(),
            Err(Error::TooLarge) => blocks(src@, i0 as int, h@, Seq::empty()) matches Some((c, _j)) ==> old(out)@.len()
                + c.len() > limit,
        },
{
    let n = src.len();
    let base = out.len();
    let bmax = h.bmax;
    let ghost goal = blocks(src@, i0 as int, h@, Seq::empty());
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
            base <= op <= out@.len(),
            op <= limit,
            limit <= MAX_OUT,
            bmax == h.bmax,
            0x1_0000 <= bmax <= 0x40_0000,
            goal == blocks(src@, i0 as int, h@, Seq::empty()),
            blocks(src@, i as int, h@, out@.subrange(base as int, op as int)) == goal,
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
                lemma_blocks_len(src@, i0 as int, h@, Seq::empty());
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
        let op2 = match decode_one(src, j, size, raw, h.indep, bmax, out, base, op) {
            Err(_) => {
                return Err(Error::Corrupt);
            },
            Ok(m) => m,
        };
        if op2 > limit {
            proof {
                lemma_blocks_len(src@, e as int, h@, out@.subrange(base as int, op2 as int));
            }
            return Err(Error::TooLarge);
        }
        i = e;
        op = op2;
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
    let n = src.len();
    let base = out.len();
    let h = match read_header(src, i) {
        None => {
            return Err(Error::Corrupt);
        },
        Some(h) => h,
    };
    let j = match decode_blocks(src, h.end, &h, out, limit) {
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
            old(out)@.subrange(base as int, op as int),
        ) == Some(final(out)@.subrange(base as int, op2 as int)),
{
    let ghost before = out@;
    let ghost cur = out@.subrange(base as int, op as int);
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
    let ghost goal = blocks(src@, h.end as int, h@, Seq::empty());
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
            goal == blocks(src@, h.end as int, h@, Seq::empty()),
            !done ==> blocks(src@, k as int, h@, out@.subrange(base as int, op as int)) == goal,
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
