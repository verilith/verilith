//! Frames, blocks and the whole input (RFC 8878 §3.1), proven against
//! `spec::decompress`.
#[allow(unused_imports)]
use crate::spec::*;
use crate::bits::*;
use crate::seq::*;
use verilith_xxhash::Xxh64;
#[cfg(verus_only)]
use verilith_core::prims::le_bytes;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// ---------------------------------------------------------------------------
// Little-endian numbers
// ---------------------------------------------------------------------------

proof fn lemma_le_sub(b: Seq<u8>, i: int, n: nat, k: nat)
    requires
        0 <= i,
        i + n <= b.len(),
        k <= n,
    ensures
        le(b, i + k, (n - k) as nat) == le_bytes(b.subrange(i, i + n), k as int, (n - k) as nat),
    decreases n - k,
{
    if k < n {
        lemma_le_sub(b, i, n, k + 1);
        assert(b.subrange(i, i + n)[k as int] == b[i + k]);
    }
}

pub proof fn lemma_le_bound(b: Seq<u8>, i: int, n: nat)
    ensures
        le(b, i, n) < pow2(8 * n),
    decreases n,
{
    if n == 0 {
        lemma2_to64();
    } else {
        lemma_le_bound(b, i + 1, (n - 1) as nat);
        lemma_pow2_adds(8, (8 * (n - 1)) as nat);
        assert(pow2(8) == 256) by {
            lemma2_to64();
        }
        assert((8 + 8 * (n - 1)) as nat == 8 * n);
        let x = le(b, i + 1, (n - 1) as nat);
        assert(b[i] as nat + 256 * x < 256 * pow2((8 * (n - 1)) as nat)) by (nonlinear_arith)
            requires
                b[i] < 256,
                x < pow2((8 * (n - 1)) as nat),
        ;
    }
}

/// The `n` (at most 8) bytes at `i`, little-endian (`le`).
pub fn le_at(b: &[u8], i: usize, n: usize) -> (r: u64)
    requires
        i + n <= b@.len(),
        b@.len() < 0x1_0000_0000_0000,
        n <= 8,
    ensures
        r as nat == le(b@, i as int, n as nat),
        n <= 4 ==> r < 0x1_0000_0000,
        n <= 3 ==> r < 0x100_0000,
        n <= 2 ==> r < 0x1_0000,
{
    proof {
        lemma_le_bound(b@, i as int, n as nat);
        if n <= 4 {
            lemma_pow2_le(8 * n as nat, 32);
        }
        if n <= 3 {
            lemma_pow2_le(8 * n as nat, 24);
        }
        if n <= 2 {
            lemma_pow2_le(8 * n as nat, 16);
        }
        lemma2_to64();
    }
    if n == 0 {
        return 0;
    }
    let s = slice_subrange(b, i, i + n);
    let r = load_tail(s, 0);
    proof {
        lemma_le_sub(b@, i as int, n as nat, 0);
    }
    r
}

// ---------------------------------------------------------------------------
// Frame header
// ---------------------------------------------------------------------------

/// A frame header, decoded.
pub struct Hdr {
    pub window: u64,
    pub fcs: Option<u64>,
    pub checksum: bool,
    pub dict_id: u64,
    pub size: usize,
}

pub open spec fn hdr_is(h: Hdr, s: Header) -> bool {
    &&& h.window as nat == s.window
    &&& match h.fcs {
        None => s.fcs is None,
        Some(f) => s.fcs == Some(f as nat),
    }
    &&& h.checksum == s.checksum
    &&& h.dict_id as nat == s.dict_id
    &&& h.size as int == s.size
}

/// The frame header at the start of `b` (`frame_header`).
pub fn frame_header_exec(b: &[u8]) -> (r: Option<Hdr>)
    requires
        b@.len() < 0x1_0000_0000_0000,
    ensures
        match frame_header(b@) {
            None => r is None,
            Some(h) => r is Some && hdr_is(r.unwrap(), h) && h.size <= b@.len() && 1 <= h.size <= 14,
        },
{
    if b.len() < 1 {
        return None;
    }
    let fhd = b[0];
    let did_flag = fhd % 4;
    let checksum = (fhd / 4) % 2 == 1;
    let reserved = (fhd / 8) % 2 == 1;
    let single = (fhd / 32) % 2 == 1;
    let fcs_flag = fhd / 64;
    let wd_size: usize = if single {
        0
    } else {
        1
    };
    let did_size: usize = if did_flag == 0 {
        0
    } else if did_flag == 1 {
        1
    } else if did_flag == 2 {
        2
    } else {
        4
    };
    let fcs_size: usize = if fcs_flag == 0 {
        if single {
            1
        } else {
            0
        }
    } else if fcs_flag == 1 {
        2
    } else if fcs_flag == 2 {
        4
    } else {
        8
    };
    let size = 1 + wd_size + did_size + fcs_size;
    if reserved || b.len() < size {
        return None;
    }
    let wlog: u64 = if single {
        0
    } else {
        b[1] as u64 / 8 + 10
    };
    let dict_id = le_at(b, 1 + wd_size, did_size);
    let fcs_raw = le_at(b, 1 + wd_size + did_size, fcs_size);
    let fcs: Option<u64> = if fcs_size == 0 {
        None
    } else if fcs_size == 2 {
        Some(fcs_raw + 256)
    } else {
        Some(fcs_raw)
    };
    if !single && wlog > 31 {
        return None;
    }
    let window: u64 = if single {
        fcs.unwrap()
    } else {
        proof {
            lemma_pow2_le(wlog as nat, 31);
            lemma_u64_pow2_no_overflow(wlog as nat);
            lemma_u64_shl_is_mul(1, wlog);
            assert(pow2(31) == 0x8000_0000) by {
                lemma2_to64();
            }
        }
        let base: u64 = 1u64 << wlog;
        let m = (b[1] % 8) as u64;
        proof {
            assert((base / 8) * m <= base) by (nonlinear_arith)
                requires
                    m <= 7,
            ;
        }
        base + (base / 8) * m
    };
    Some(Hdr { window, fcs, checksum, dict_id, size })
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// `compressed_block` only appends.
proof fn lemma_cb_grows(b: Seq<u8>, window: nat, bmax: nat, st: FrameState)
    ensures
        compressed_block(b, window, bmax, st) is Some ==> compressed_block(b, window, bmax, st).unwrap().out.len()
            >= st.out.len(),
{
    if let Some(l) = lit_section(b, bmax, st.huf) {
        let st1 = FrameState { huf: l.huf, ..st };
        let c = b.subrange(l.used, b.len() as int);
        lemma_seq_section(c, l.lits, window, st1);
        if let Some((n, h)) = nb_seq(c) {
            if n != 0 && h + 1 <= c.len() && c[h] % 4 == 0 {
                if let Some((t, a3)) = seq_hdr(c, h, st1) {
                    let s = c.subrange(a3, c.len() as int);
                    if let Some(p) = bstart(s) {
                        if t.ll.log + t.of.log + t.ml.log <= p {
                            let st0 = SeqState {
                                p: p - t.ll.log - t.of.log - t.ml.log,
                                sll: bits(s, p - t.ll.log, t.ll.log),
                                sof: bits(s, p - t.ll.log - t.of.log, t.of.log),
                                sml: bits(s, p - t.ll.log - t.of.log - t.ml.log, t.ml.log),
                                reps: st1.reps,
                                li: 0,
                                out: st1.out,
                            };
                            lemma_seq_run_grows(t, s, l.lits, window, n, st0);
                        }
                    }
                }
            }
        }
    }
}

/// `blocks_r` only appends.
pub proof fn lemma_blocks_grows(b: Seq<u8>, i: int, window: nat, reach: nat, st: FrameState)
    ensures
        blocks_r(b, i, window, reach, st) is Some ==> blocks_r(b, i, window, reach, st).unwrap().1.out.len()
            >= st.out.len(),
    decreases b.len() - i,
{
    if i >= 0 && i + 3 <= b.len() {
        let bh = le(b, i, 3);
        let size = bh / 8;
        let c = i + 3;
        let bmax = min(window as int, BLOCK_MAX as int) as nat;
        if c + size <= b.len() {
            lemma_cb_grows(b.subrange(c, c + size), reach, bmax, st);
            if let Some(st2) = compressed_block(b.subrange(c, c + size), reach, bmax, st) {
                lemma_blocks_grows(b, c + size, window, reach, st2);
            }
            lemma_blocks_grows(b, c + size, window, reach, FrameState { out: st.out + b.subrange(c, c + size), ..st });
        }
        if c + 1 <= b.len() {
            lemma_blocks_grows(b, c + 1, window, reach, FrameState { out: st.out + Seq::new(size, |k: int| b[c]), ..st });
        }
    }
}

/// One raw, RLE or compressed block at `i`. Returns the position after it.
#[verifier::rlimit(30)]
pub fn block_exec(
    b: &[u8],
    i: usize,
    window: u64,
    reach: u64,
    d: &mut FrameDec,
    olimit: usize,
    Ghost(st): Ghost<FrameState>,
) -> (r: (
    Step,
    usize,
    bool,
))
    requires
        b@.len() < 0x1_0000_0000_0000,
        i + 3 <= b@.len(),
        dec_is(old(d), st),
        old(d).out@.len() <= olimit <= 0x1_0000_0000_0000,
    ensures
        ({
            let bh = le(b@, i as int, 3);
            let last = bh % 2 == 1;
            let ty = (bh / 2) % 4;
            let size = bh / 8;
            let bmax = min(window as int, BLOCK_MAX as int) as nat;
            let c = i + 3;
            let spec: Option<(int, FrameState)> = if size > bmax {
                None
            } else if ty == 0 {
                if c + size > b@.len() {
                    None
                } else {
                    Some((c + size, FrameState { out: st.out + b@.subrange(c as int, c + size), ..st }))
                }
            } else if ty == 1 {
                if c + 1 > b@.len() {
                    None
                } else {
                    Some((c + 1, FrameState { out: st.out + Seq::new(size, |k: int| b@[c as int]), ..st }))
                }
            } else if ty == 2 {
                if c + size > b@.len() {
                    None
                } else {
                    match compressed_block(b@.subrange(c as int, c + size), reach as nat, bmax, st) {
                        None => None,
                        Some(st2) => Some((c + size, st2)),
                    }
                }
            } else {
                None
            };
            &&& r.2 == last
            &&& match spec {
                None => !(r.0 is Done),
                Some((j, st2)) => match r.0 {
                    Step::Done => {
                        &&& r.1 as int == j
                        &&& dec_is(final(d), st2)
                        &&& final(d).fstart == old(d).fstart
                        &&& final(d).out@.subrange(0, old(d).fstart as int) == old(d).out@.subrange(
                            0,
                            old(d).fstart as int,
                        )
                        &&& final(d).out@.len() <= olimit
                    },
                    Step::Bad => false,
                    Step::Limit => old(d).fstart + st2.out.len() > olimit,
                },
            }
        }),
{
    let ghost pre = d.out@.subrange(0, d.fstart as int);
    let bh = le_at(b, i, 3);
    let last = bh % 2 == 1;
    let ty = (bh / 2) % 4;
    let size = (bh / 8) as usize;
    let bmax: usize = if window < 131072 {
        window as usize
    } else {
        131072
    };
    let c = i + 3;
    if size > bmax {
        return (Step::Bad, 0, last);
    }
    if ty == 0 {
        if size > b.len() - c {
            return (Step::Bad, 0, last);
        }
        if size > olimit - d.out.len() {
            return (Step::Limit, 0, last);
        }
        let ghost o0 = d.out@;
        d.out.extend_from_slice(slice_subrange(b, c, c + size));
        proof {
            assert(d.out@.subrange(0, d.fstart as int) =~= pre);
            assert(fout(d.out@, d.fstart as int) =~= st.out + b@.subrange(c as int, c + size));
        }
        (Step::Done, c + size, last)
    } else if ty == 1 {
        if c + 1 > b.len() {
            return (Step::Bad, 0, last);
        }
        if size > olimit - d.out.len() {
            return (Step::Limit, 0, last);
        }
        let x = b[c];
        let ghost o0 = fout(d.out@, d.fstart as int);
        let mut k: usize = 0;
        while k < size
            invariant
                k <= size,
                d.fstart <= d.out@.len(),
                d.out@.len() == old(d).out@.len() + k,
                d.out@.subrange(0, d.fstart as int) == pre,
                fout(d.out@, d.fstart as int) == o0 + Seq::new(k as nat, |q: int| x),
            decreases size - k,
        {
            let ghost before = d.out@;
            d.out.push(x);
            proof {
                assert(d.out@.subrange(0, d.fstart as int) =~= pre);
                assert(fout(d.out@, d.fstart as int) =~= fout(before, d.fstart as int).push(x));
                assert(Seq::new((k + 1) as nat, |q: int| x) =~= Seq::new(k as nat, |q: int| x).push(x));
                assert(fout(d.out@, d.fstart as int) =~= o0 + Seq::new((k + 1) as nat, |q: int| x));
            }
            k = k + 1;
        }
        proof {
            assert(Seq::new(size as nat, |q: int| x) =~= Seq::new(size as nat, |q: int| b@[c as int]));
        }
        (Step::Done, c + 1, last)
    } else if ty == 2 {
        if size > b.len() - c {
            return (Step::Bad, 0, last);
        }
        let res = compressed_block_exec(slice_subrange(b, c, c + size), reach, bmax, d, olimit, Ghost(st));
        (res, c + size, last)
    } else {
        (Step::Bad, 0, last)
    }
}

/// The blocks of a frame from `i` on (`blocks`).
/// With `hashing`, each block's output is fed to `hash` as it is made,
/// while it is still in cache.
pub fn blocks_exec(
    b: &[u8],
    i0: usize,
    window: u64,
    reach: u64,
    d: &mut FrameDec,
    olimit: usize,
    hash: &mut Xxh64,
    hashing: bool,
    Ghost(st): Ghost<FrameState>,
) -> (r: (Step, usize))
    requires
        b@.len() < 0x1_0000_0000_0000,
        i0 <= b@.len(),
        dec_is(old(d), st),
        old(d).out@.len() <= olimit <= 0x1_0000_0000_0000,
        hashing ==> old(hash).is(st.out),
        hashing ==> reach == window,
    ensures
        hashing && r.0 is Done ==> final(hash).is(blocks_r(b@, i0 as int, window as nat, reach as nat, st).unwrap().1.out),
        match blocks_r(b@, i0 as int, window as nat, reach as nat, st) {
            None => !(r.0 is Done),
            Some((j, st2)) => match r.0 {
                Step::Done => {
                    &&& r.1 as int == j
                    &&& dec_is(final(d), st2)
                    &&& final(d).fstart == old(d).fstart
                    &&& final(d).out@.subrange(0, old(d).fstart as int) == old(d).out@.subrange(0, old(d).fstart as int)
                    &&& final(d).out@.len() <= olimit
                },
                Step::Bad => false,
                Step::Limit => old(d).fstart + st2.out.len() > olimit,
            },
        },
{
    let ghost full = blocks_r(b@, i0 as int, window as nat, reach as nat, st);
    let ghost pre = d.out@.subrange(0, d.fstart as int);
    let ghost fs = d.fstart;
    let ghost mut cur = st;
    let mut i = i0;
    loop
        invariant
            b@.len() < 0x1_0000_0000_0000,
            i <= b@.len(),
            dec_is(d, cur),
            d.fstart == fs,
            fs == old(d).fstart,
            pre == old(d).out@.subrange(0, fs as int),
            d.out@.subrange(0, fs as int) == pre,
            d.out@.len() <= olimit <= 0x1_0000_0000_0000,
            full == blocks_r(b@, i0 as int, window as nat, reach as nat, st),
            blocks_r(b@, i as int, window as nat, reach as nat, cur) == full,
            hashing ==> hash.is(cur.out),
            hashing ==> reach == window,
        decreases b@.len() - i,
    {
        if i + 3 > b.len() {
            return (Step::Bad, 0);
        }
        let ghost prev = cur;
        let before = d.out.len();
        let (res, j, last) = block_exec(b, i, window, reach, d, olimit, Ghost(cur));
        match res {
            Step::Done => {},
            _ => {
                proof {
                    let bh = le(b@, i as int, 3);
                    let size = bh / 8;
                    let c = i + 3;
                    lemma_blocks_grows(b@, c + size, window as nat, reach as nat, FrameState { out: prev.out + b@.subrange(c as int, c + size), ..prev });
                    lemma_blocks_grows(b@, c + 1, window as nat, reach as nat, FrameState { out: prev.out + Seq::new(size, |k: int| b@[c as int]), ..prev });
                    let bmax = min(window as int, BLOCK_MAX as int) as nat;
                    if c + size <= b@.len() {
                        if let Some(st2) = compressed_block(b@.subrange(c as int, c + size), reach as nat, bmax, prev) {
                            lemma_blocks_grows(b@, c + size, window as nat, reach as nat, st2);
                        }
                    }
                }
                return (res, 0);
            },
        }
        proof {
            let bh = le(b@, i as int, 3);
            let size = bh / 8;
            let c = i + 3;
            let bmax = min(window as int, BLOCK_MAX as int) as nat;
            cur = if (bh / 2) % 4 == 0 {
                FrameState { out: prev.out + b@.subrange(c as int, c + size), ..prev }
            } else if (bh / 2) % 4 == 1 {
                FrameState { out: prev.out + Seq::new(size, |k: int| b@[c as int]), ..prev }
            } else {
                compressed_block(b@.subrange(c as int, c + size), reach as nat, bmax, prev).unwrap()
            };
        }
        if hashing {
            proof {
                crate::stream::lemma_block_step_prefix(b@, i as int, window as nat, reach as nat, prev);
                assert(crate::stream::block_step(b@, i as int, window as nat, reach as nat, prev).unwrap().1 == cur);
                assert(before == fs + prev.out.len());
            }
            let new = slice_subrange(d.out.as_slice(), before, d.out.len());
            proof {
                assert(cur.out =~= prev.out + new@);
            }
            hash.update(new, Ghost(prev.out));
        }
        if last {
            return (Step::Done, j);
        }
        i = j;
    }
}

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

/// Starts a new frame at the end of `d.out`.
pub fn reset(d: &mut FrameDec)
    ensures
        dec_is(final(d), initial_state()),
        final(d).out@ == old(d).out@,
        final(d).fstart == old(d).out@.len(),
        final(d).lits@ == old(d).lits@,
{
    d.fstart = d.out.len();
    d.r1 = 1;
    d.r2 = 4;
    d.r3 = 8;
    d.huf = None;
    d.seqt = None;
    proof {
        assert(fout(d.out@, d.fstart as int) =~= Seq::<u8>::empty());
    }
}

/// One Zstandard frame at `i` (`frame`), appended to `d.out`.
#[verifier::rlimit(30)]
fn frame_exec(b: &[u8], i: usize, d: &mut FrameDec, olimit: usize) -> (r: (Step, usize))
    requires
        b@.len() < 0x1_0000_0000_0000,
        i + 4 <= b@.len(),
        old(d).out@.len() <= olimit <= 0x1_0000_0000_0000,
    ensures
        match frame(b@, i as int) {
            None => !(r.0 is Done),
            Some((j, o)) => match r.0 {
                Step::Done => {
                    &&& r.1 as int == j
                    &&& final(d).out@ == old(d).out@ + o
                    &&& final(d).out@.len() <= olimit
                },
                Step::Bad => false,
                Step::Limit => old(d).out@.len() + o.len() > olimit,
            },
        },
{
    let ghost o0 = d.out@;
    let h = match frame_header_exec(slice_subrange(b, i + 4, b.len())) {
        None => {
            return (Step::Bad, 0);
        },
        Some(h) => h,
    };
    if h.dict_id != 0 {
        return (Step::Bad, 0);
    }
    reset(d);
    // Room for the declared content size up front, so the output is not
    // copied as it grows. Capped by the limit and at 64 MiB, so a header
    // alone cannot make it allocate much.
    match h.fcs {
        Some(f) => {
            let room = (olimit - d.out.len()) as u64;
            let want = if f < room { f } else { room };
            let want = if want < 0x400_0000 { want } else { 0x400_0000 };
            d.out.reserve(want as usize + 64);
        },
        None => {},
    }
    let mut hash = Xxh64::new();
    let (res, j) = blocks_exec(b, i + 4 + h.size, h.window, h.window, d, olimit, &mut hash, h.checksum, Ghost(initial_state()));
    match res {
        Step::Done => {},
        _ => {
            return (res, 0);
        },
    }
    let fstart = d.fstart;
    let n = d.out.len() - fstart;
    proof {
        assert(o0.subrange(0, o0.len() as int) =~= o0);
        assert(d.out@ =~= o0 + fout(d.out@, fstart as int));
        let fo = fout(d.out@, fstart as int);
        assert(fo.subrange(0, fo.len() as int) =~= fo);
        assert(h.window + no_dict().st.out.len() == h.window);
    }
    match h.fcs {
        Some(f) => {
            if f != n as u64 {
                return (Step::Bad, 0);
            }
        },
        None => {},
    }
    if h.checksum {
        if j > b.len() || b.len() - j < 4 {
            return (Step::Bad, 0);
        }
        let x = hash.digest(Ghost(fout(d.out@, fstart as int)));
        let want = le_at(b, j, 4);
        let lo = x & 0xFFFF_FFFF;
        proof {
            assert(x & 0xFFFF_FFFF == x % 0x1_0000_0000) by (bit_vector);
        }
        if want != lo {
            return (Step::Bad, 0);
        }
        (Step::Done, j + 4)
    } else {
        (Step::Done, j)
    }
}

/// Is the 4-byte number at `i` a skippable frame's magic?
pub fn is_skippable(m: u64) -> (r: bool)
    ensures
        r == skippable(m as nat),
{
    m / 16 == 0x184D2A5
}

/// Why decompression failed.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Error {
    /// The input is not valid Zstandard data (`decompress` is `None`).
    Corrupt,
    /// The output would pass the limit.
    TooLarge,
}

/// Decompresses all frames of `b` (`decompress`), giving up once the
/// output would pass `limit` bytes.
pub fn decompress_exec(b: &[u8], limit: usize) -> (r: Result<Vec<u8>, Error>)
    requires
        b@.len() < 0x1_0000_0000_0000,
        limit <= 0x1_0000_0000_0000,
    ensures
        match r {
            Ok(v) => decompress(b@) == Some(v@) && v@.len() <= limit,
            Err(Error::Corrupt) => decompress(b@) is None,
            Err(Error::TooLarge) => decompress(b@) is None || decompress(b@).unwrap().len() > limit,
        },
{
    decompress_reuse(b, limit, Vec::new())
}

/// As `decompress_exec`, writing into `buf`'s storage: its old contents are
/// dropped and its capacity is reused, which saves the allocation and the
/// first-touch page faults when a caller decodes many inputs.
pub fn decompress_reuse(b: &[u8], limit: usize, buf: Vec<u8>) -> (r: Result<Vec<u8>, Error>)
    requires
        b@.len() < 0x1_0000_0000_0000,
        limit <= 0x1_0000_0000_0000,
    ensures
        match r {
            Ok(v) => decompress(b@) == Some(v@) && v@.len() <= limit,
            Err(Error::Corrupt) => decompress(b@) is None,
            Err(Error::TooLarge) => decompress(b@) is None || decompress(b@).unwrap().len() > limit,
        },
{
    let mut buf = buf;
    buf.clear();
    let mut d = FrameDec {
        out: buf,
        fstart: 0,
        r1: 1,
        r2: 4,
        r3: 8,
        huf: None,
        seqt: None,
        lits: Vec::new(),
    };
    let ghost full = decompress(b@);
    let mut i: usize = 0;
    proof {
        assert(d.out@ =~= Seq::<u8>::empty());
    }
    loop
        invariant
            b@.len() < 0x1_0000_0000_0000,
            limit <= 0x1_0000_0000_0000,
            i <= b@.len(),
            d.out@.len() <= limit,
            full == decompress(b@),
            frames(b@, i as int, d.out@) == full,
        decreases b@.len() - i,
    {
        if i == b.len() {
            return Ok(d.out);
        }
        if b.len() - i < 5 {
            return Err(Error::Corrupt);
        }
        let m = le_at(b, i, 4);
        if is_skippable(m) {
            if b.len() - i < 8 {
                return Err(Error::Corrupt);
            }
            let size = le_at(b, i + 4, 4);
            if size + 8 >= 0x1_0000_0000 || size as usize > b.len() - i - 8 {
                return Err(Error::Corrupt);
            }
            i = i + 8 + size as usize;
        } else if m != 0xFD2FB528 {
            return Err(Error::Corrupt);
        } else {
            let ghost o0 = d.out@;
            let (res, j) = frame_exec(b, i, &mut d, limit);
            match res {
                Step::Done => {},
                Step::Bad => {
                    return Err(Error::Corrupt);
                },
                Step::Limit => {
                    proof {
                        if let Some((j2, o)) = frame(b@, i as int) {
                            if j2 > i && j2 <= b@.len() {
                                lemma_frames_grows(b@, j2, o0 + o);
                            }
                        }
                    }
                    return Err(Error::TooLarge);
                },
            }
            if j <= i || j > b.len() {
                return Err(Error::Corrupt);
            }
            i = j;
        }
    }
}

/// `frames` only appends.
proof fn lemma_frames_grows(b: Seq<u8>, i: int, out: Seq<u8>)
    ensures
        frames(b, i, out) is Some ==> frames(b, i, out).unwrap().len() >= out.len(),
    decreases b.len() - i,
{
    if 0 <= i && i + 5 <= b.len() {
        let m = le(b, i, 4);
        if skippable(m) {
            let size = le(b, i + 4, 4);
            if i + 8 <= b.len() && size + 8 < 0x1_0000_0000 && i + 8 + size <= b.len() {
                lemma_frames_grows(b, i + 8 + size, out);
            }
        } else if let Some((j, o)) = frame(b, i) {
            if j > i && j <= b.len() {
                lemma_frames_grows(b, j, out + o);
            }
        }
    }
}

} // verus!

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::Corrupt => "corrupt Zstandard data",
            Error::TooLarge => "the output would be larger than the limit",
        })
    }
}

impl std::error::Error for Error {}
