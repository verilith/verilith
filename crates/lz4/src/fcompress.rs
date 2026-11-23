//! The frame compressor, proven to produce a frame that `spec::frame`
//! decodes back to the input: a header, the input cut into blocks of the
//! chosen maximum size (each compressed, or stored when that is not
//! smaller), the end mark, and the checksums asked for.
use crate::compress::{compress_block_counted, compress_small_counted, BIG_SIZE, HASH_SIZE};
#[cfg(verus_only)]
use crate::compress::{extends, lemma_seqs_pre, lemma_strict_block};
use crate::frame::*;
use crate::spec::*;
use verilith_xxhash::xxh32_exec;
use verilith_core::prims::{copy_in, extend, set};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// What kind of frame to write.
#[derive(Debug, Clone, Copy)]
pub struct Prefs {
    /// Block maximum size: 4 to 7 for 64 KiB, 256 KiB, 1 MiB, 4 MiB
    /// (anything lower is 4, anything higher 7).
    pub block_id: u8,
    /// Independent blocks (otherwise matches reach into earlier blocks,
    /// which compresses better).
    pub indep: bool,
    /// A checksum after each block.
    pub bsum: bool,
    /// A checksum of the content at the end.
    pub csum: bool,
    /// The content size in the header.
    pub csize: bool,
    /// liblz4's acceleration: 1 is the default; larger is faster and
    /// compresses less.
    pub accel: usize,
}

/// `x` in `n` bytes, little-endian.
pub open spec fn le_seq(x: nat, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![(x % 256) as u8] + le_seq(x / 256, (n - 1) as nat)
    }
}

/// `x` fits in `n` bytes.
pub open spec fn fits(x: nat, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        x == 0
    } else {
        fits(x / 256, (n - 1) as nat)
    }
}

proof fn lemma_le_seq_len(x: nat, n: nat)
    ensures
        le_seq(x, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_le_seq_len(x / 256, (n - 1) as nat);
    }
}

/// `le` reads back what `le_seq` wrote.
proof fn lemma_le_seq(s: Seq<u8>, i: int, x: nat, n: nat)
    requires
        0 <= i,
        i + n <= s.len(),
        s.subrange(i, i + n) == le_seq(x, n),
        fits(x, n),
    ensures
        le(s, i, n) == x,
    decreases n,
{
    lemma_le_seq_len(x, n);
    if n > 0 {
        let r = le_seq(x / 256, (n - 1) as nat);
        lemma_le_seq_len(x / 256, (n - 1) as nat);
        assert(s[i] == s.subrange(i, i + n)[0]);
        assert(le_seq(x, n)[0] == (x % 256) as u8);
        assert(s.subrange(i + 1, i + n) =~= r) by {
            assert forall|k: int| 0 <= k < n - 1 implies s.subrange(i + 1, i + n)[k] == r[k] by {
                assert(s.subrange(i, i + n)[k + 1] == le_seq(x, n)[k + 1]);
            }
        }
        lemma_le_seq(s, i + 1, x / 256, (n - 1) as nat);
    }
}

/// `le` depends only on the bytes it reads.
proof fn lemma_le_same(b: Seq<u8>, c: Seq<u8>, i: int, n: nat)
    requires
        0 <= i,
        i + n <= b.len(),
        i + n <= c.len(),
        forall|x: int| i <= x < i + n ==> b[x] == c[x],
    ensures
        le(b, i, n) == le(c, i, n),
    decreases n,
{
    if n > 0 {
        lemma_le_same(b, c, i + 1, (n - 1) as nat);
    }
}

fn push_le32(v: &mut Vec<u8>, x: u32)
    ensures
        final(v)@ == old(v)@ + le_seq(x as nat, 4),
{
    v.push((x % 256) as u8);
    v.push(((x / 256) % 256) as u8);
    v.push(((x / 65536) % 256) as u8);
    v.push((x / 16777216) as u8);
    proof {
        reveal_with_fuel(le_seq, 5);
        let xn = x as nat;
        assert(xn / 256 / 256 == xn / 65536);
        assert(xn / 256 / 256 / 256 == xn / 16777216);
        assert(final(v)@ =~= old(v)@ + le_seq(xn, 4));
    }
}

fn push_le64(v: &mut Vec<u8>, x: u64)
    ensures
        final(v)@ == old(v)@ + le_seq(x as nat, 8),
{
    let lo = (x % 0x1_0000_0000) as u32;
    let hi = (x / 0x1_0000_0000) as u32;
    push_le32(v, lo);
    push_le32(v, hi);
    proof {
        lemma_le_seq_split(x as nat);
        assert(final(v)@ =~= old(v)@ + (le_seq(lo as nat, 4) + le_seq(hi as nat, 4)));
    }
}

proof fn lemma_le_seq_split(x: nat)
    ensures
        le_seq(x, 8) == le_seq(x % 0x1_0000_0000, 4) + le_seq(x / 0x1_0000_0000, 4),
{
    reveal_with_fuel(le_seq, 9);
    let lo = x % 0x1_0000_0000;
    let hi = x / 0x1_0000_0000;
    assert(x / 256 / 256 / 256 / 256 == hi);
    assert(lo % 256 == x % 256);
    assert((lo / 256) % 256 == (x / 256) % 256);
    assert((lo / 256 / 256) % 256 == (x / 256 / 256) % 256);
    assert((lo / 256 / 256 / 256) % 256 == (x / 256 / 256 / 256) % 256);
    assert(le_seq(x, 8) =~= le_seq(lo, 4) + le_seq(hi, 4));
}

/// The frame's blocks so far: whatever is written after `p`, reading the
/// blocks from the header's end is reading them from the end of `p` with
/// the content `out`.
pub open spec fn breach(p: Seq<u8>, h: Header, out: Seq<u8>) -> bool {
    forall|s: Seq<u8>| #[trigger]
        extends(p, s) ==> blocks(s, h.end, h, Seq::empty(), Seq::empty()) == blocks(s, p.len() as int, h, Seq::empty(), out)
}

/// A block as the compressor writes it.
pub open spec fn enc_block(data: Seq<u8>, raw: bool, bsum: bool) -> Seq<u8> {
    le_seq(
        (data.len() + if raw {
            0x8000_0000nat
        } else {
            0
        }) as nat,
        4,
    ) + data + if bsum {
        le_seq(xxh32(data) as nat, 4)
    } else {
        Seq::empty()
    }
}

proof fn lemma_fits32(x: nat)
    requires
        x < 0x1_0000_0000,
    ensures
        fits(x, 4),
{
    reveal_with_fuel(fits, 5);
    assert(x / 256 / 256 / 256 / 256 == 0);
}

/// Reading a block the compressor wrote.
proof fn lemma_block_at(s: Seq<u8>, i: int, h: Header, out: Seq<u8>, data: Seq<u8>, raw: bool, out2: Seq<u8>)
    requires
        0 <= i,
        i + enc_block(data, raw, h.bsum).len() <= s.len(),
        s.subrange(i, i + enc_block(data, raw, h.bsum).len()) == enc_block(data, raw, h.bsum),
        0 < data.len() <= h.bmax,
        h.bmax <= 0x40_0000,
        block_data(data, raw, h.indep, Seq::empty(), out) == Some(out2),
        out2.len() - out.len() <= h.bmax,
    ensures
        blocks(s, i, h, Seq::empty(), out) == blocks(s, i + enc_block(data, raw, h.bsum).len(), h, Seq::empty(), out2),
{
    hide(block_data);
    let e = enc_block(data, raw, h.bsum);
    let w = (data.len() + if raw {
        0x8000_0000nat
    } else {
        0
    }) as nat;
    let size = data.len() as int;
    let c = xxh32(data) as nat;
    lemma_le_seq_len(w, 4);
    lemma_le_seq_len(c, 4);
    assert(e.len() == 4 + size + if h.bsum {
        4int
    } else {
        0
    });
    assert forall|x: int| 0 <= x < e.len() implies s[i + x] == e[x] by {
        assert(s.subrange(i, i + e.len())[x] == e[x]);
    }
    assert(s.subrange(i, i + 4) =~= le_seq(w, 4)) by {
        assert forall|x: int| 0 <= x < 4 implies s[i + x] == le_seq(w, 4)[x] by {
            assert(e[x] == le_seq(w, 4)[x]);
        }
    }
    lemma_fits32(w);
    lemma_le_seq(s, i, w, 4);
    let j = i + 4;
    assert(s.subrange(j, j + size) =~= data) by {
        assert forall|x: int| 0 <= x < size implies s[j + x] == data[x] by {
            assert(e[4 + x] == data[x]);
        }
    }
    if h.bsum {
        assert(s.subrange(j + size, j + size + 4) =~= le_seq(c, 4)) by {
            assert forall|x: int| 0 <= x < 4 implies s[j + size + x] == le_seq(c, 4)[x] by {
                assert(e[4 + size + x] == le_seq(c, 4)[x]);
            }
        }
        lemma_fits32(c);
        lemma_le_seq(s, j + size, c, 4);
    }
    assert(w % 0x8000_0000 == size);
    assert((w >= 0x8000_0000) == raw);
}

proof fn lemma_breach_step(p: Seq<u8>, h: Header, out: Seq<u8>, data: Seq<u8>, raw: bool, out2: Seq<u8>)
    requires
        breach(p, h, out),
        0 < data.len() <= h.bmax,
        h.bmax <= 0x40_0000,
        block_data(data, raw, h.indep, Seq::empty(), out) == Some(out2),
        out2.len() - out.len() <= h.bmax,
    ensures
        breach(p + enc_block(data, raw, h.bsum), h, out2),
{
    let e = enc_block(data, raw, h.bsum);
    let p2 = p + e;
    assert forall|s: Seq<u8>| #[trigger] extends(p2, s) implies blocks(s, h.end, h, Seq::empty(), Seq::empty()) == blocks(
        s,
        p2.len() as int,
        h,
        Seq::empty(),
        out2,
    ) by {
        let i = p.len() as int;
        assert forall|x: int| 0 <= x < p2.len() implies s[x] == p2[x] by {
            assert(s.subrange(0, p2.len() as int)[x] == p2[x]);
        }
        assert(s.subrange(0, i) =~= p);
        assert(extends(p, s));
        assert(s.subrange(i, i + e.len()) =~= e);
        lemma_block_at(s, i, h, out, data, raw, out2);
    }
}

/// Writes a frame header for these choices.
fn write_header(v: &mut Vec<u8>, id: u8, indep: bool, bsum: bool, csize: bool, csum: bool, n: usize) -> (h: Ghost<
    Header,
>)
    requires
        old(v)@.len() == 0,
        4 <= id <= 7,
    ensures
        header(final(v)@, 0) == Some(h@),
        h@.end == final(v)@.len(),
        h@.indep == indep,
        h@.bsum == bsum,
        h@.csum == csum,
        h@.csize == if csize {
            Some(n as nat)
        } else {
            None
        },
        h@.bmax == block_max(id as nat),
        final(v)@.len() <= 15,
{
    push_le32(v, 0x184D2204);
    proof {
        lemma_le_seq_len(0x184D2204, 4);
    }
    let flg: u8 = 64 + (if indep {
        32u8
    } else {
        0
    }) + (if bsum {
        16u8
    } else {
        0
    }) + (if csize {
        8u8
    } else {
        0
    }) + (if csum {
        4u8
    } else {
        0
    });
    let bd: u8 = id * 16;
    v.push(flg);
    v.push(bd);
    if csize {
        push_le64(v, n as u64);
        proof {
            lemma_le_seq_len(n as nat, 8);
        }
    }
    let ghost dlen: int = if csize {
        10
    } else {
        2
    };
    assert(v@.len() == 4 + dlen);
    let hc = ((xxh32_exec(slice_subrange(v.as_slice(), 4, v.len())) / 256) % 256) as u8;
    let ghost desc = v@.subrange(4, 4 + dlen);
    v.push(hc);
    let ghost h = Header {
        indep,
        bsum,
        csize: if csize {
            Some(n as nat)
        } else {
            None
        },
        csum,
        dict: None,
        bmax: block_max(id as nat),
        end: v@.len() as int,
    };
    proof {
        let s = v@;
        assert(s.subrange(0, 4) =~= le_seq(0x184D2204, 4));
        lemma_fits32(0x184D2204);
        lemma_le_seq(s, 0, 0x184D2204, 4);
        if csize {
            assert(s.subrange(6, 14) =~= le_seq(n as nat, 8));
            assert(fits(n as nat, 8)) by {
                reveal_with_fuel(fits, 9);
                let x = n as nat;
                assert(x / 256 / 256 / 256 / 256 / 256 / 256 / 256 / 256 == 0);
            }
            lemma_le_seq(s, 6, n as nat, 8);
        }
        assert(s[4] == flg && s[5] == bd);
        assert(s.subrange(4, 4 + dlen) =~= desc);
        assert(s[4 + dlen] == hc);
        let f = flg as nat;
        let b = bd as nat;
        assert(f / 64 == 1 && (f / 2) % 2 == 0 && f % 2 == 0);
        assert(((f / 8) % 2 == 1) == csize);
        assert(((f / 32) % 2 == 1) == indep);
        assert(((f / 16) % 2 == 1) == bsum);
        assert(((f / 4) % 2 == 1) == csum);
        assert(b / 128 == 0 && b % 16 == 0 && (b / 16) % 8 == id);
    }
    Ghost(h)
}

/// The index after a header with these fields, when it starts at 0.
pub open spec fn header_len(csize: bool) -> int {
    if csize {
        15
    } else {
        7
    }
}

/// A header read at 0 reads the same from any longer input.
proof fn lemma_header_ext(p: Seq<u8>, s: Seq<u8>)
    requires
        extends(p, s),
        header(p, 0).is_some(),
    ensures
        header(s, 0) == header(p, 0),
{
    assert forall|x: int| 0 <= x < p.len() implies s[x] == p[x] by {
        assert(s.subrange(0, p.len() as int)[x] == p[x]);
    }
    lemma_le_same(p, s, 0, 4);
    let flg = p[4] as nat;
    let has_size = (flg / 8) % 2 == 1;
    let has_dict = flg % 2 == 1;
    let dlen: int = 2 + (if has_size {
        8int
    } else {
        0
    }) + (if has_dict {
        4int
    } else {
        0
    });
    assert(s.subrange(4, 4 + dlen) =~= p.subrange(4, 4 + dlen));
    if has_size {
        lemma_le_same(p, s, 6, 8);
    }
    if has_dict {
        lemma_le_same(p, s, 4 + dlen - 4, 4);
    }
}

/// Compresses `input` as one frame.
#[inline(always)]
pub fn compress(input: &[u8], prefs: &Prefs) -> (v: Vec<u8>)
    ensures
        frame(v@, 0) == Some((input@, v@.len() as int)),
        frames(v@, 0) == Some(input@),
{
    compress_counted(input, prefs).0
}

/// A bound on the frame compressors' steps (each loop turn, each byte
/// compared, copied, cleared or summed).
pub open spec fn frame_work(n: nat) -> nat {
    24 * n + 20000
}

/// `compress`, with its steps counted.
pub fn compress_counted(input: &[u8], prefs: &Prefs) -> (res: (Vec<u8>, Ghost<nat>))
    ensures
        frame(res.0@, 0) == Some((input@, res.0@.len() as int)),
        frames(res.0@, 0) == Some(input@),
        res.1@ <= frame_work(input@.len()),
{
    let n = input.len();
    let id: u8 = if prefs.block_id < 4 {
        4
    } else if prefs.block_id > 7 {
        7
    } else {
        prefs.block_id
    };
    let bmax: usize = if id == 4 {
        0x1_0000
    } else if id == 5 {
        0x4_0000
    } else if id == 6 {
        0x10_0000
    } else {
        0x40_0000
    };
    let accel = if prefs.accel < 1 {
        1
    } else if prefs.accel > 65537 {
        65537
    } else {
        prefs.accel
    };
    let mut v: Vec<u8> = Vec::new();
    let Ghost(h) = write_header(&mut v, id, prefs.indep, prefs.bsum, prefs.csize, prefs.csum, n);
    let ghost hp = v@;
    let mut table = [0u32;BIG_SIZE];
    // Room for a block compressed with no checks, but no more than the
    // input needs: a short input does not clear a 4 MiB buffer.
    let sc: usize = if n < bmax && n + n / 255 + 16 < bmax {
        n + n / 255 + 16
    } else {
        bmax
    };
    let mut scratch: Vec<u8> = vec![0u8; sc];
    let ghost mut work: nat = (hp.len() + BIG_SIZE + sc) as nat;
    let mut st: usize = 0;
    proof {
        assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(breach(v@, h, Seq::empty()));
        assert(v@.subrange(0, hp.len() as int) =~= hp);
    }
    while st < n
        invariant
            n == input@.len(),
            st <= n,
            scratch@.len() == sc,
            sc <= 2 * n + 16,
            st < n ==> work <= 2 * n + 4127 + 21 * st,
            work <= 2 * n + 4127 + 21 * st + 12357,
            forall|x: int| 0 <= x < BIG_SIZE ==> (#[trigger] table@[x]) <= st,
            bmax == h.bmax,
            0x1_0000 <= bmax <= 0x40_0000,
            1 <= accel <= 65537,
            h.indep == prefs.indep,
            h.bsum == prefs.bsum,
            extends(hp, v@),
            breach(v@, h, input@.subrange(0, st as int)),
        decreases n - st,
    {
        let en = if n - st > bmax {
            st + bmax
        } else {
            n
        };
        let ghost p = v@;
        let ghost out0 = input@.subrange(0, st as int);
        let ghost out2 = input@.subrange(0, en as int);
        let ghost chunk = input@.subrange(st as int, en as int);
        let size = en - st;
        let (lo, r, Ghost(w)) = block(input, st, en, scratch.as_mut_slice(), 0, &mut table, accel, prefs.indep);
        proof {
            work = (work + 1 + w) as nat;
        }
        let stored = match r {
            Some(m) => m >= size,
            None => true,
        };
        if stored {
            push_le32(&mut v, (size + 0x8000_0000) as u32);
            let data = slice_subrange(input, st, en);
            extend(&mut v, data);
            proof {
                work = (work + 4 + size) as nat;
                if prefs.bsum {
                    work = (work + 4 + size) as nat;
                }
            }
            if prefs.bsum {
                push_le32(&mut v, xxh32_exec(data));
            }
            proof {
                assert(v@ =~= p + enc_block(chunk, true, h.bsum));
                assert(out0 + chunk =~= out2);
                lemma_breach_step(p, h, out0, chunk, true, out2);
            }
        } else {
            let m = r.unwrap();
            assert(scratch@.subrange(0, m as int).len() == m);
            push_le32(&mut v, m as u32);
            let data = slice_subrange(scratch.as_slice(), 0, m);
            extend(&mut v, data);
            proof {
                work = (work + 4 + m) as nat;
                if prefs.bsum {
                    work = (work + 4 + m) as nat;
                }
            }
            if prefs.bsum {
                push_le32(&mut v, xxh32_exec(data));
            }
            proof {
                assert(v@ =~= p + enc_block(data@, false, h.bsum));
                lemma_block_ok(data@, input@, lo as int, st as int, en as int, h.indep);
                lemma_breach_step(p, h, out0, data@, false, out2);
            }
        }
        proof {
            assert(extends(hp, v@)) by {
                assert(v@.subrange(0, hp.len() as int) =~= p.subrange(0, hp.len() as int));
            }
        }
        st = en;
    }
    let ghost p = v@;
    push_le32(&mut v, 0);
    let ghost mid = v@;
    proof {
        work = (work + 4) as nat;
        if prefs.csum {
            work = (work + n + 4) as nat;
        }
    }
    if prefs.csum {
        push_le32(&mut v, xxh32_exec(input));
    }
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
        assert(v@ =~= p + le_seq(0, 4) + if h.csum {
            le_seq(xxh32(input@) as nat, 4)
        } else {
            Seq::empty()
        });
        lemma_frame_end(hp, p, h, input@, v@);
    }
    (v, Ghost(work))
}

/// A bound on `block`'s steps (each loop turn, each byte compared or
/// copied, each table entry cleared).
pub open spec fn block_work(size: nat) -> nat {
    18 * size + BIG_SIZE as nat + HASH_SIZE as nat + 60
}

/// Compresses the block `input[st..en]` of a frame into `dst` from `base`
/// on, with the earlier blocks as history unless blocks are independent
/// (or the frame is too long for the table's 32-bit positions, where
/// history is given up; a block may always do without). Gives where the
/// history starts and what `compress_block` gives.
fn block(
    input: &[u8],
    st: usize,
    en: usize,
    dst: &mut [u8],
    base: usize,
    table: &mut [u32; BIG_SIZE],
    accel: usize,
    indep: bool,
) -> (r: (usize, Option<usize>, Ghost<nat>))
    requires
        st <= en <= input@.len(),
        en - st <= 0x40_0000,
        1 <= accel <= 65537,
        base <= old(dst)@.len(),
        forall|x: int| 0 <= x < BIG_SIZE ==> (#[trigger] old(table)@[x]) <= st,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.subrange(0, base as int) == old(dst)@.subrange(0, base as int),
        forall|x: int| 0 <= x < BIG_SIZE ==> (#[trigger] final(table)@[x]) <= en,
        r.0 == st || (r.0 == 0 && !indep),
        r.1 matches Some(n) ==> base <= n <= final(dst)@.len() && block_strict(
            final(dst)@.subrange(base as int, n as int),
            input@.subrange(r.0 as int, st as int),
            (en - st) as nat,
        ) == Some(input@.subrange(r.0 as int, en as int)),
        r.2@ <= block_work((en - st) as nat),
{
    if indep || en > 0xf000_0000 {
        if en - st <= 65536 {
            let (c, w) = compress_small_counted(input, st, st, en, dst, base, accel);
            (st, c, w)
        } else {
            let mut i: usize = 0;
            while i < BIG_SIZE
                invariant
                    i <= BIG_SIZE,
                    forall|x: int| 0 <= x < i ==> (#[trigger] table@[x]) == 0,
                decreases BIG_SIZE - i,
            {
                table[i] = 0;
                i = i + 1;
            }
            let (c, Ghost(w)) = compress_block_counted(input, st, st, en, dst, base, table, accel);
            (st, c, Ghost((BIG_SIZE + w) as nat))
        }
    } else {
        let (c, w) = compress_block_counted(input, 0, st, en, dst, base, table, accel);
        (0, c, w)
    }
}

/// What `block` wrote is the block the frame needs after its earlier
/// content, linked or not.
proof fn lemma_block_ok(data: Seq<u8>, input: Seq<u8>, lo: int, st: int, en: int, indep: bool)
    requires
        0 <= lo <= st <= en <= input.len(),
        lo == st || (lo == 0 && !indep),
        block_strict(data, input.subrange(lo, st), (en - st) as nat) == Some(input.subrange(lo, en)),
    ensures
        block_data(data, false, indep, Seq::empty(), input.subrange(0, st)) == Some(input.subrange(0, en)),
{
    let out0 = input.subrange(0, st);
    let out2 = input.subrange(0, en);
    let chunk = input.subrange(st, en);
    let hist = input.subrange(lo, st);
    let size = (en - st) as nat;
    lemma_block_data_nodict(data, false, indep, out0);
    assert(out0 + chunk =~= out2);
    if lo == st {
        assert(hist =~= Seq::<u8>::empty());
        if indep {
            lemma_strict_block(data, 0, Seq::empty(), size);
        } else {
            lemma_seqs_pre(data, 0, out0, Seq::empty(), size);
            assert(out0 + Seq::<u8>::empty() =~= out0);
            lemma_strict_block(data, 0, out0, (out0.len() + size) as nat);
        }
    } else {
        lemma_strict_block(data, 0, hist, (hist.len() + size) as nat);
    }
}

/// Writes `x` at `d`, little-endian.
fn put_le32(dst: &mut [u8], d: usize, x: u32)
    requires
        d + 4 <= old(dst)@.len(),
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|k: int|
            0 <= k < final(dst)@.len() ==> #[trigger] final(dst)@[k] == if d <= k < d + 4 {
                le_seq(x as nat, 4)[k - d]
            } else {
                old(dst)@[k]
            },
{
    let n = dst.len();
    set(dst, d, (x % 256) as u8);
    set(dst, d + 1, ((x / 256) % 256) as u8);
    set(dst, d + 2, ((x / 65536) % 256) as u8);
    set(dst, d + 3, (x / 16777216) as u8);
    proof {
        reveal_with_fuel(le_seq, 5);
        let xn = x as nat;
        assert(xn / 256 / 256 == xn / 65536);
        assert(xn / 256 / 256 / 256 == xn / 16777216);
        lemma_le_seq_len(xn, 4);
        let e = le_seq(xn, 4);
        assert(e[0] == (xn % 256) as u8);
        assert(e[1] == ((xn / 256) % 256) as u8);
        assert(e[2] == ((xn / 65536) % 256) as u8);
        assert(e[3] == (xn / 16777216) as u8);
    }
}

/// Writes the block `input[st..en]` of a frame at `d`: its size, then
/// the data compressed straight into place, or stored when that is not
/// smaller, then its checksum if asked. Gives where it ends, and (for the
/// proof) the data and whether it was stored. `None`: `dst` is too small.
#[verifier::rlimit(100)]
fn put_block(
    input: &[u8],
    st: usize,
    en: usize,
    dst: &mut [u8],
    d: usize,
    table: &mut [u32; BIG_SIZE],
    accel: usize,
    indep: bool,
    bsum: bool,
) -> (res: (Option<(usize, Ghost<Seq<u8>>, Ghost<bool>)>, Ghost<nat>))
    requires
        st < en <= input@.len(),
        en - st <= 0x40_0000,
        1 <= accel <= 65537,
        d <= old(dst)@.len(),
        forall|x: int| 0 <= x < BIG_SIZE ==> (#[trigger] old(table)@[x]) <= st,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        forall|x: int| 0 <= x < BIG_SIZE ==> (#[trigger] final(table)@[x]) <= en,
        res.0 matches Some((e2, data, raw)) ==> {
            &&& d <= e2 <= final(dst)@.len()
            &&& final(dst)@.subrange(0, e2 as int) == old(dst)@.subrange(0, d as int) + enc_block(data@, raw@, bsum)
            &&& 0 < data@.len() <= en - st
            &&& block_data(data@, raw@, indep, Seq::empty(), input@.subrange(0, st as int)) == Some(input@.subrange(0, en as int))
        },
        // The block's, then each byte written or summed.
        res.1@ <= block_work((en - st) as nat) + 2 * (en - st) + 8,
{
    let dn = dst.len();
    let ghost p = dst@.subrange(0, d as int);
    let ghost out0 = input@.subrange(0, st as int);
    let ghost out2 = input@.subrange(0, en as int);
    let ghost chunk = input@.subrange(st as int, en as int);
    let size = en - st;
    if dn - d < 4 {
        return (None, Ghost(0));
    }
    let base = d + 4;
    let ghost s0 = dst@;
    let (lo, r, Ghost(w0)) = block(input, st, en, dst, base, table, accel, indep);
    let ghost mut work: nat = (w0 + 4) as nat;
    let ghost s1 = dst@;
    proof {
        assert forall|x: int| 0 <= x < base implies s1[x] == s0[x] by {
            assert(s1.subrange(0, base as int)[x] == s0.subrange(0, base as int)[x]);
        }
    }
    let fits = match r {
        Some(e) => e - base < size,
        None => false,
    };
    let mut e2: usize;
    let ghost data: Seq<u8>;
    if fits {
        let e = r.unwrap();
        let m = e - base;
        put_le32(dst, d, m as u32);
        e2 = e;
        proof {
            data = s1.subrange(base as int, e as int);
            lemma_le_seq_len(m as nat, 4);
            assert(dst@.subrange(0, e2 as int) =~= p + le_seq(m as nat, 4) + data);
            assert(dst@.subrange(base as int, e2 as int) =~= data);
            lemma_block_ok(data, input@, lo as int, st as int, en as int, indep);
            assert(data.len() > 0);
        }
    } else {
        if dn - base < size {
            return (None, Ghost(work));
        }
        proof {
            work = (work + size) as nat;
        }
        put_le32(dst, d, (size + 0x8000_0000) as u32);
        copy_in(dst, base, input, st, size);
        e2 = base + size;
        proof {
            data = chunk;
            lemma_le_seq_len((size + 0x8000_0000) as nat, 4);
            assert(dst@.subrange(0, e2 as int) =~= p + le_seq((size + 0x8000_0000) as nat, 4) + data);
            assert(dst@.subrange(base as int, e2 as int) =~= data);
            assert(out0 + chunk =~= out2);
        }
    }
    let ghost s3 = dst@;
    if bsum {
        if dn - e2 < 4 {
            return (None, Ghost(work));
        }
        proof {
            work = (work + (e2 - base) + 4) as nat;
        }
        let c = xxh32_exec(slice_subrange(dst, base, e2));
        put_le32(dst, e2, c);
        proof {
            lemma_le_seq_len(c as nat, 4);
            assert(dst@.subrange(0, e2 + 4) =~= s3.subrange(0, e2 as int) + le_seq(c as nat, 4));
        }
        e2 = e2 + 4;
    }
    proof {
        assert(dst@.subrange(0, e2 as int) =~= p + enc_block(data, !fits, bsum));
    }
    (Some((e2, Ghost(data), Ghost(!fits))), Ghost(work))
}

/// Compresses `input` as one frame into `dst`, each block written
/// straight to its place. `Some(m)`: `dst[..m]` is the frame. `None`:
/// `dst` is too small.
#[inline(always)]
pub fn compress_into(input: &[u8], dst: &mut [u8], prefs: &Prefs) -> (r: Option<usize>)
    ensures
        final(dst)@.len() == old(dst)@.len(),
        r matches Some(m) ==> m <= final(dst)@.len() && frame(final(dst)@.subrange(0, m as int), 0) == Some(
            (input@, m as int),
        ) && frames(final(dst)@.subrange(0, m as int), 0) == Some(input@),
{
    compress_into_counted(input, dst, prefs).0
}

/// `compress_into`, with its steps counted.
pub fn compress_into_counted(input: &[u8], dst: &mut [u8], prefs: &Prefs) -> (res: (Option<usize>, Ghost<nat>))
    ensures
        final(dst)@.len() == old(dst)@.len(),
        res.0 matches Some(m) ==> m <= final(dst)@.len() && frame(final(dst)@.subrange(0, m as int), 0) == Some(
            (input@, m as int),
        ) && frames(final(dst)@.subrange(0, m as int), 0) == Some(input@),
        res.1@ <= frame_work(input@.len()),
{
    let n = input.len();
    let dn = dst.len();
    let id: u8 = if prefs.block_id < 4 {
        4
    } else if prefs.block_id > 7 {
        7
    } else {
        prefs.block_id
    };
    let bmax: usize = if id == 4 {
        0x1_0000
    } else if id == 5 {
        0x4_0000
    } else if id == 6 {
        0x10_0000
    } else {
        0x40_0000
    };
    let accel = if prefs.accel < 1 {
        1
    } else if prefs.accel > 65537 {
        65537
    } else {
        prefs.accel
    };
    let mut hv: Vec<u8> = Vec::new();
    let Ghost(h) = write_header(&mut hv, id, prefs.indep, prefs.bsum, prefs.csize, prefs.csum, n);
    let ghost hp = hv@;
    let hl = hv.len();
    if hl > dn {
        return (None, Ghost(0));
    }
    copy_in(dst, 0, hv.as_slice(), 0, hl);
    let mut d: usize = hl;
    let mut table = [0u32;BIG_SIZE];
    let ghost mut work: nat = (hl + BIG_SIZE) as nat;
    let mut st: usize = 0;
    proof {
        assert(dst@.subrange(0, d as int) =~= hp);
        assert(hp.subrange(0, hp.len() as int) =~= hp);
        assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(breach(hp, h, Seq::empty()));
    }
    while st < n
        invariant
            n == input@.len(),
            dn == dst@.len(),
            dn == old(dst)@.len(),
            st <= n,
            d <= dn,
            bmax == h.bmax,
            0x1_0000 <= bmax <= 0x40_0000,
            1 <= accel <= 65537,
            h.indep == prefs.indep,
            h.bsum == prefs.bsum,
            forall|x: int| 0 <= x < BIG_SIZE ==> (#[trigger] table@[x]) <= st,
            st < n ==> work <= 4111 + 21 * st,
            work <= 4111 + 21 * st + 12357,
            extends(hp, dst@.subrange(0, d as int)),
            breach(dst@.subrange(0, d as int), h, input@.subrange(0, st as int)),
        decreases n - st,
    {
        let en = if n - st > bmax {
            st + bmax
        } else {
            n
        };
        let ghost p = dst@.subrange(0, d as int);
        let ghost out0 = input@.subrange(0, st as int);
        let ghost out2 = input@.subrange(0, en as int);
        let (pb, Ghost(w)) = put_block(input, st, en, dst, d, &mut table, accel, prefs.indep, prefs.bsum);
        proof {
            work = (work + 1 + w) as nat;
        }
        let e2 = match pb {
            None => {
                return (None, Ghost(work));
            },
            Some((e2, data, raw)) => {
                proof {
                    lemma_breach_step(p, h, out0, data@, raw@, out2);
                    assert(extends(hp, dst@.subrange(0, e2 as int))) by {
                        assert(dst@.subrange(0, e2 as int).subrange(0, hp.len() as int) =~= p.subrange(
                            0,
                            hp.len() as int,
                        ));
                    }
                }
                e2
            },
        };
        d = e2;
        st = en;
    }
    let ghost p = dst@.subrange(0, d as int);
    if dn - d < 4 {
        return (None, Ghost(work));
    }
    proof {
        work = (work + 4) as nat;
    }
    put_le32(dst, d, 0);
    let ghost s4 = dst@;
    proof {
        lemma_le_seq_len(0, 4);
        assert(dst@.subrange(0, d + 4) =~= p + le_seq(0, 4));
    }
    d = d + 4;
    if prefs.csum {
        if dn - d < 4 {
            return (None, Ghost(work));
        }
        proof {
            work = (work + n + 4) as nat;
        }
        let c = xxh32_exec(input);
        put_le32(dst, d, c);
        proof {
            lemma_le_seq_len(c as nat, 4);
            assert(dst@.subrange(0, d + 4) =~= s4.subrange(0, d as int) + le_seq(c as nat, 4));
        }
        d = d + 4;
    }
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
        let s = dst@.subrange(0, d as int);
        assert(s =~= p + le_seq(0, 4) + if h.csum {
            le_seq(xxh32(input@) as nat, 4)
        } else {
            Seq::empty()
        });
        lemma_frame_end(hp, p, h, input@, s);
    }
    (Some(d), Ghost(work))
}

/// The end mark, and the content checksum after it.
proof fn lemma_end_blocks(p: Seq<u8>, h: Header, input: Seq<u8>, s: Seq<u8>)
    requires
        breach(p, h, input),
        s == p + le_seq(0, 4) + if h.csum {
            le_seq(xxh32(input) as nat, 4)
        } else {
            Seq::empty()
        },
    ensures
        blocks(s, h.end, h, Seq::empty(), Seq::empty()) == Some((input, (p.len() + 4) as int)),
        h.csum ==> s.len() == p.len() + 8 && le(s, (p.len() + 4) as int, 4) == xxh32(input),
        !h.csum ==> s.len() == p.len() + 4,
{
    let c = xxh32(input) as nat;
    lemma_le_seq_len(0, 4);
    lemma_le_seq_len(c, 4);
    let i = p.len() as int;
    let j = i + 4;
    assert(s.subrange(0, i) =~= p);
    assert(extends(p, s));
    assert(s.subrange(i, i + 4) =~= le_seq(0, 4));
    lemma_fits32(0);
    lemma_le_seq(s, i, 0, 4);
    assert(blocks(s, i, h, Seq::empty(), input) == Some((input, j)));
    if h.csum {
        assert(s.subrange(j, j + 4) =~= le_seq(c, 4));
        lemma_fits32(c);
        lemma_le_seq(s, j, c, 4);
    }
}

/// The end of a frame the compressor wrote.
proof fn lemma_frame_end(hp: Seq<u8>, p: Seq<u8>, h: Header, input: Seq<u8>, s: Seq<u8>)
    requires
        header(hp, 0) == Some(h),
        h.end == hp.len(),
        extends(hp, p),
        breach(p, h, input),
        h.csize matches Some(c) ==> c == input.len(),
        s == p + le_seq(0, 4) + if h.csum {
            le_seq(xxh32(input) as nat, 4)
        } else {
            Seq::empty()
        },
    ensures
        frame(s, 0) == Some((input, s.len() as int)),
        frames(s, 0) == Some(input),
{
    lemma_end_blocks(p, h, input, s);
    assert(extends(hp, s)) by {
        assert(s.subrange(0, hp.len() as int) =~= p.subrange(0, hp.len() as int));
    }
    lemma_header_ext(hp, s);
    assert(frame(s, 0) == Some((input, s.len() as int)));
    lemma_frames_one(s, input);
}

/// Input that is exactly one frame.
proof fn lemma_frames_one(s: Seq<u8>, input: Seq<u8>)
    requires
        frame(s, 0) == Some((input, s.len() as int)),
    ensures
        frames(s, 0) == Some(input),
{
    assert(header(s, 0).is_some());
    assert(le(s, 0, 4) == MAGIC);
    assert(skippable(s, 0).is_none());
    assert(frames(s, s.len() as int) == Some(Seq::<u8>::empty()));
    assert(s.len() >= 7);
    assert(input + Seq::<u8>::empty() =~= input);
}

} // verus!
