//! One-shot compression (RFC 8878), proven to round-trip: the output of
//! `compress_exec` is a single Zstandard frame, and `spec::decompress` of
//! it is exactly the input.
//!
//! The frame header, the block headers, raw blocks and RLE blocks are
//! proven by construction. A compressed block is made by the encoder
//! (`enc`, which is only proven memory safe) and then checked by the
//! verified block decoder (`frame::block_exec`), which keeps the decoder's
//! state across blocks: the block is kept only if it decodes, by the spec,
//! to exactly the input it stands for, and otherwise it is replaced by a
//! raw block. So the round trip holds whatever the encoder does.
#[allow(unused_imports)]
use crate::spec::*;
use crate::enc::Enc;
use crate::frame::*;
use crate::seq::*;
#[cfg(verus_only)]
use crate::huf::huf_opt_is;
#[cfg(verus_only)]
use crate::stream::{block_step, body_len, lemma_block_step_local, lemma_blocks_unfold, lemma_le_local, prefix};
#[cfg(verus_only)]
use crate::bits::lemma_pow2_le;
#[cfg(verus_only)]
use vstd::bits::*;
use crate::work::Meter;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

// ---------------------------------------------------------------------------
// Little-endian numbers
// ---------------------------------------------------------------------------

/// `le` of one more byte.
proof fn lemma_le_snoc(b: Seq<u8>, i: int, k: nat)
    requires
        0 <= i,
        i + k + 1 <= b.len(),
    ensures
        le(b, i, k + 1) == le(b, i, k) + pow2(8 * k) * b[i + k],
    decreases k,
{
    if k == 0 {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(le(b, i + 1, 0) == 0);
        assert(le(b, i, 1) == b[i] as nat + 256 * le(b, i + 1, 0));
        assert(le(b, i, 0) == 0);
        assert(8 * k == 0);
        assert(pow2(8 * k) == 1);
        assert(b[i + k] == b[i]);
        assert((k + 1) as nat == 1);
        assert(le(b, i, (k + 1) as nat) == le(b, i, 1));
        let q = pow2(8 * k);
        let y = b[i + k] as nat;
        assert(q * y == y) by (nonlinear_arith)
            requires
                q == 1,
        ;
    } else {
        lemma_le_snoc(b, i + 1, (k - 1) as nat);
        lemma_pow2_adds(8, (8 * (k - 1)) as nat);
        assert(pow2(8) == 256) by {
            lemma2_to64();
        }
        assert((8 + 8 * (k - 1)) as nat == 8 * k);
        let x = le(b, i + 1, (k - 1) as nat);
        let p = pow2((8 * (k - 1)) as nat);
        let y = b[i + k] as nat;
        assert(((k - 1) + 1) as nat == k);
        assert(b[i + 1 + (k - 1)] == b[i + k]);
        assert(le(b, i + 1, k) == x + p * y);
        assert(le(b, i, k + 1) == b[i] as nat + 256 * le(b, i + 1, k));
        assert(le(b, i, k) == b[i] as nat + 256 * x);
        assert(pow2(8 * k) == 256 * p);
        let q = pow2(8 * k);
        let l1 = le(b, i, k + 1);
        let l0 = le(b, i, k);
        let bi = b[i] as nat;
        assert(l1 == l0 + q * y) by (nonlinear_arith)
            requires
                l1 == bi + 256 * (x + p * y),
                l0 == bi + 256 * x,
                q == 256 * p,
        ;
        assert(le(b, i, k + 1) == le(b, i, k) + pow2(8 * k) * b[i + k]);
    }
}

/// `le` reads only the bytes it covers.
proof fn lemma_le_same(a: Seq<u8>, b: Seq<u8>, i: int, n: nat)
    requires
        0 <= i,
        i + n <= a.len(),
        i + n <= b.len(),
        forall|k: int| i <= k < i + n ==> a[k] == b[k],
    ensures
        le(a, i, n) == le(b, i, n),
    decreases n,
{
    if n > 0 {
        lemma_le_same(a, b, i + 1, (n - 1) as nat);
    }
}

/// Appends the `n` bytes of `x`, little-endian.
fn push_le(v: &mut Vec<u8>, x: u64, n: usize)
    requires
        n <= 8,
        x as nat <= pow2(8 * n as nat) - 1,
    ensures
        final(v)@.len() == old(v)@.len() + n,
        final(v)@.subrange(0, old(v)@.len() as int) == old(v)@,
        le(final(v)@, old(v)@.len() as int, n as nat) == x,
{
    let ghost l0 = v@.len() as int;
    let mut y = x;
    let mut k: usize = 0;
    proof {
        assert(pow2(0) == 1) by {
            lemma2_to64();
        }
        assert(8 * (k as nat) == 0);
        assert(le(v@, l0, 0) == 0);
        assert(pow2(8 * k as nat) * y == y) by (nonlinear_arith)
            requires
                pow2(8 * k as nat) == 1,
        ;
    }
    while k < n
        invariant
            k <= n <= 8,
            v@.len() == l0 + k,
            v@.subrange(0, l0) == old(v)@,
            l0 == old(v)@.len(),
            x as nat == le(v@, l0, k as nat) + pow2(8 * k as nat) * y,
        decreases n - k,
    {
        let ghost v0 = v@;
        let byte = (y % 256) as u8;
        v.push(byte);
        proof {
            lemma_le_same(v0, v@, l0, k as nat);
            lemma_le_snoc(v@, l0, k as nat);
            lemma_pow2_adds(8 * k as nat, 8);
            assert(pow2(8) == 256) by {
                lemma2_to64();
            }
            assert((8 * k + 8) as nat == 8 * (k + 1) as nat);
            let p = pow2(8 * k as nat);
            lemma_fundamental_div_mod(y as int, 256);
            assert(p * y == p * (y % 256) + (p * 256) * (y / 256)) by (nonlinear_arith)
                requires
                    y == 256 * (y / 256) + y % 256,
            ;
            assert(v@.subrange(0, l0) =~= old(v)@);
        }
        y = y / 256;
        k = k + 1;
    }
    proof {
        let p = pow2(8 * n as nat);
        assert(p * y <= x) by (nonlinear_arith)
            requires
                x as nat == le(v@, l0, n as nat) + p * y,
        ;
        if y > 0 {
            assert(p * y >= p) by (nonlinear_arith)
                requires
                    y >= 1,
                    p >= 0,
            ;
        }
    }
}

// ---------------------------------------------------------------------------
// Frame header
// ---------------------------------------------------------------------------

/// `frame_header` reads only the header's own bytes.
proof fn lemma_fh_ext(a: Seq<u8>, b: Seq<u8>)
    requires
        frame_header(a) is Some,
        frame_header(a).unwrap().size <= a.len() <= b.len(),
        b.subrange(0, a.len() as int) == a,
    ensures
        frame_header(b) == frame_header(a),
{
    assert forall|k: int| 0 <= k < a.len() implies a[k] == b[k] by {
        assert(b.subrange(0, a.len() as int)[k] == b[k]);
    }
    let fhd = a[0];
    let did_flag = fhd % 4;
    let single = (fhd / 32) % 2 == 1;
    let fcs_flag = fhd / 64;
    let wd_size: int = if single {
        0
    } else {
        1
    };
    let did_size: int = if did_flag == 0 {
        0
    } else if did_flag == 1 {
        1
    } else if did_flag == 2 {
        2
    } else {
        4
    };
    let fcs_size: int = if fcs_flag == 0 {
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
    lemma_le_same(a, b, 1 + wd_size, did_size as nat);
    lemma_le_same(a, b, 1 + wd_size + did_size, fcs_size as nat);
}

/// The frame header for `n` bytes of content: single segment (the window
/// is the content size) when `single`, otherwise a window of `2^wlog`.
/// Returns the window and the header size.
fn put_header(out: &mut Vec<u8>, n: u64, single: bool, wlog: u32, checksum: bool) -> (r: (u64, usize))
    requires
        !single ==> 10 <= wlog <= 31 && n >= 256,
    ensures
        final(out)@.len() == old(out)@.len() + r.1,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        frame_header(final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int)) == Some(
            Header {
                window: r.0 as nat,
                fcs: Some(n as nat),
                checksum: checksum,
                dict_id: 0,
                size: r.1 as int,
            },
        ),
        single ==> r.0 == n,
        !single ==> r.0 as nat == pow2(wlog as nat),
{
    let ghost l0 = out@.len() as int;
    let f: u8 = if n < 256 && single {
        0
    } else if n < 65536 + 256 {
        1
    } else if n <= 0xFFFF_FFFF {
        2
    } else {
        3
    };
    let s: u8 = if single {
        1
    } else {
        0
    };
    let c: u8 = if checksum {
        1
    } else {
        0
    };
    let fhd: u8 = f * 64 + s * 32 + c * 4;
    out.push(fhd);
    let ghost lf = out@;
    let mut size: usize = 1;
    let mut window: u64 = n;
    if !single {
        let wb: u8 = ((wlog - 10) * 8) as u8;
        out.push(wb);
        size = 2;
        proof {
            lemma_pow2_le(wlog as nat, 31);
            lemma_u64_pow2_no_overflow(wlog as nat);
            lemma_u64_shl_is_mul(1, wlog as u64);
            assert(pow2(31) == 0x8000_0000) by {
                lemma2_to64();
            }
        }
        window = 1u64 << wlog;
    }
    let ghost l1 = out@.len() as int;
    let ghost ow = out@;
    proof {
        assert(ow[l0] == fhd);
        assert(!single ==> ow[l0 + 1] == ((wlog - 10) * 8) as u8);
        assert(ow.subrange(0, l0) =~= old(out)@);
    }
    proof {
        lemma2_to64();
        lemma_pow2_adds(32, 32);
        assert(pow2(64) == 0x1_0000_0000_0000_0000);
        assert(pow2(16) == 0x1_0000);
        assert(pow2(8) == 0x100);
        assert(pow2(32) == 0x1_0000_0000);
    }
    let fsz: usize = if f == 0 {
        push_le(out, n, 1);
        1
    } else if f == 1 {
        push_le(out, n - 256, 2);
        2
    } else if f == 2 {
        push_le(out, n, 4);
        4
    } else {
        push_le(out, n, 8);
        8
    };
    size = size + fsz;
    proof {
        let h = out@.subrange(l0, out@.len() as int);
        assert(out@.subrange(0, l1) == ow);
        assert(out@[l0] == ow[l0]);
        assert(out@.subrange(0, l0) =~= old(out)@) by {
            assert(out@.subrange(0, l0) =~= ow.subrange(0, l0));
        }
        assert(h[0] == fhd);
        assert(fhd % 4 == 0);
        assert((fhd / 4) % 2 == 1 <==> checksum);
        assert((fhd / 8) % 2 == 0);
        assert((fhd / 32) % 2 == 1 <==> single);
        assert(fhd / 64 == f);
        assert(out@.subrange(l1, l1 + fsz as int) =~= h.subrange(l1 - l0, l1 - l0 + fsz as int));
        lemma_le_local(out@, l1, h, l1 - l0, fsz as nat);
        if !single {
            assert(out@[l0 + 1] == ow[l0 + 1]);
            assert(h[1] == ((wlog - 10) * 8) as u8);
            assert(h[1] / 8 + 10 == wlog);
            assert(h[1] % 8 == 0);
            assert(pow2(wlog as nat) / 8 * 0 == 0);
        }
        assert(le(h, 1 + (size - 1 - fsz), 0) == 0);
    }
    (window, size)
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// The 3-byte block header of a block of `size` bytes and type `ty`.
fn put_block_header(out: &mut Vec<u8>, size: usize, ty: u8, last: bool)
    requires
        size < 0x20_0000,
        ty < 4,
    ensures
        final(out)@.len() == old(out)@.len() + 3,
        final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
        ({
            let bh = le(final(out)@, old(out)@.len() as int, 3);
            &&& bh % 2 == 1 <==> last
            &&& (bh / 2) % 4 == ty
            &&& bh / 8 == size
        }),
{
    let l: u64 = if last {
        1
    } else {
        0
    };
    let bh: u64 = (size as u64) * 8 + (ty as u64) * 2 + l;
    proof {
        assert(pow2(24) == 0x100_0000) by {
            lemma2_to64();
        }
        assert(bh % 2 == l) by (nonlinear_arith)
            requires
                bh == (size as u64) * 8 + (ty as u64) * 2 + l,
                l < 2,
        ;
        assert((bh / 2) % 4 == ty) by (nonlinear_arith)
            requires
                bh == (size as u64) * 8 + (ty as u64) * 2 + l,
                l < 2,
                ty < 4,
        ;
        assert(bh / 8 == size) by (nonlinear_arith)
            requires
                bh == (size as u64) * 8 + (ty as u64) * 2 + l,
                l < 2,
                ty < 4,
        ;
    }
    push_le(out, bh, 3);
}

/// The output so far ends with whole blocks from `h0` on, which take the
/// state from the frame's start to `cur`: whatever follows them,
/// decoding the blocks from `h0` is decoding what follows from `at`
/// (the end of `o`) in state `cur`.
pub open spec fn chain(o: Seq<u8>, h0: int, w: nat, cur: FrameState) -> bool {
    forall|t: Seq<u8>| #[trigger]
        blocks_r(o + t, h0, w, w, initial_state()) == blocks_r(o + t, o.len() as int, w, w, cur)
}

/// Appending a non-last block `u` that steps from `cur` to `nxt` keeps the
/// chain.
proof fn lemma_chain_step(o: Seq<u8>, u: Seq<u8>, h0: int, w: nat, cur: FrameState, nxt: FrameState)
    requires
        chain(o, h0, w, cur),
        3 <= u.len(),
        3 + body_len(u) <= u.len(),
        block_step(u, 0, w, w, cur) == Some((u.len() as int, nxt, false)),
    ensures
        chain(o + u, h0, w, nxt),
{
    assert forall|t: Seq<u8>| #[trigger]
        blocks_r((o + u) + t, h0, w, w, initial_state()) == blocks_r((o + u) + t, (o + u).len() as int, w, w, nxt) by {
        let b = (o + u) + t;
        assert(o + (u + t) =~= b);
        assert(b.subrange(o.len() as int, (o.len() + u.len()) as int) =~= u);
        lemma_block_step_local(b, o.len() as int, u, w, w, cur);
        lemma_blocks_unfold(b, o.len() as int, w, w, cur);
        assert(blocks_r(o + (u + t), h0, w, w, initial_state()) == blocks_r(o + (u + t), o.len() as int, w, w, cur));
    }
}

/// Appending the last block `u`, stepping from `cur` to `fin`: the blocks
/// from `h0` decode to `fin`, whatever follows.
proof fn lemma_chain_last(o: Seq<u8>, u: Seq<u8>, h0: int, w: nat, cur: FrameState, fin: FrameState, t: Seq<u8>)
    requires
        chain(o, h0, w, cur),
        3 <= u.len(),
        3 + body_len(u) <= u.len(),
        block_step(u, 0, w, w, cur) == Some((u.len() as int, fin, true)),
    ensures
        blocks_r((o + u) + t, h0, w, w, initial_state()) == Some(((o + u).len() as int, fin)),
{
    let b = (o + u) + t;
    assert(o + (u + t) =~= b);
    assert(b.subrange(o.len() as int, (o.len() + u.len()) as int) =~= u);
    lemma_block_step_local(b, o.len() as int, u, w, w, cur);
    lemma_blocks_unfold(b, o.len() as int, w, w, cur);
    assert(blocks_r(o + (u + t), h0, w, w, initial_state()) == blocks_r(o + (u + t), o.len() as int, w, w, cur));
}

/// A raw block of `data` steps from `st` to `st` with `data` appended.
proof fn lemma_raw_step(u: Seq<u8>, data: Seq<u8>, w: nat, st: FrameState, last: bool)
    requires
        u.len() == 3 + data.len(),
        u.subrange(3, u.len() as int) == data,
        ({
            let bh = le(u, 0, 3);
            &&& bh % 2 == 1 <==> last
            &&& (bh / 2) % 4 == 0
            &&& bh / 8 == data.len()
        }),
        data.len() <= min(w as int, BLOCK_MAX as int),
    ensures
        3 + body_len(u) <= u.len(),
        block_step(u, 0, w, w, st) == Some((u.len() as int, FrameState { out: st.out + data, ..st }, last)),
{
}

/// An RLE block of `size` copies of `x`.
proof fn lemma_rle_step(u: Seq<u8>, x: u8, size: nat, w: nat, st: FrameState, last: bool)
    requires
        u.len() == 4,
        u[3] == x,
        ({
            let bh = le(u, 0, 3);
            &&& bh % 2 == 1 <==> last
            &&& (bh / 2) % 4 == 1
            &&& bh / 8 == size
        }),
        size <= min(w as int, BLOCK_MAX as int),
    ensures
        3 + body_len(u) <= u.len(),
        block_step(u, 0, w, w, st) == Some((4int, FrameState { out: st.out + Seq::new(size, |k: int| x), ..st }, last)),
{
    assert(Seq::new(size, |k: int| u[3]) =~= Seq::new(size, |k: int| x));
}

/// Are all of `src[a..b]` equal to `x`?
fn all_eq(src: &[u8], a: usize, b: usize, x: u8) -> (r: bool)
    requires
        a <= b <= src@.len(),
    ensures
        r ==> forall|k: int| a <= k < b ==> src@[k] == x,
{
    let mut i = a;
    while i < b
        invariant
            a <= i <= b <= src@.len(),
            forall|k: int| a <= k < i ==> src@[k] == x,
        decreases b - i,
    {
        if src[i] != x {
            return false;
        }
        i = i + 1;
    }
    true
}

/// Is `x[a..a + n]` equal to `y[b..b + n]`?
fn same(x: &[u8], a: usize, y: &[u8], b: usize, n: usize) -> (r: bool)
    requires
        a + n <= x@.len(),
        b + n <= y@.len(),
    ensures
        r ==> x@.subrange(a as int, a + n) == y@.subrange(b as int, b + n),
{
    let xl = x.len();
    let yl = y.len();
    let mut i: usize = 0;
    while n - i >= 8
        invariant
            i <= n,
            xl == x@.len(),
            yl == y@.len(),
            a + n <= x@.len(),
            b + n <= y@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] x@[a + k] == y@[b + k],
        decreases n - i,
    {
        let u = verilith_core::prims::load_u64_le(x, a + i);
        let v = verilith_core::prims::load_u64_le(y, b + i);
        if u != v {
            return false;
        }
        proof {
            assert forall|k: int| 0 <= k < i + 8 implies #[trigger] x@[a + k] == y@[b + k] by {
                if k >= i {
                    let q = (k - i) as u64;
                    verilith_core::lz::lemma_word_byte(x@, (a + i) as int, u, q);
                    verilith_core::lz::lemma_word_byte(y@, (b + i) as int, v, q);
                }
            }
        }
        i = i + 8;
    }
    while i < n
        invariant
            i <= n,
            xl == x@.len(),
            yl == y@.len(),
            a + n <= x@.len(),
            b + n <= y@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] x@[a + k] == y@[b + k],
        decreases n - i,
    {
        if x[a + i] != y[b + i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < n implies #[trigger] x@.subrange(a as int, a + n)[k] == y@.subrange(b as int, b + n)[k] by {
            assert(x@[a + k] == y@[b + k]);
        }
        assert(x@.subrange(a as int, a + n) =~= y@.subrange(b as int, b + n));
    }
    true
}

// ---------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------

/// The largest input `compress_exec` takes.
#[cfg(target_pointer_width = "64")]
pub const IN_MAX: usize = 0x4000_0000_0000;

#[cfg(target_pointer_width = "32")]
pub const IN_MAX: usize = 0x7000_0000;

/// Compression parameters.
#[derive(Clone, Copy)]
pub struct Params {
    /// Base-2 log of the largest window (10 to 31).
    pub wlog: u32,
    /// Add the content checksum.
    pub checksum: bool,
    /// The encoder's level.
    pub level: i32,
}

/// `decompress` of one whole frame, at the start of `b`.
proof fn lemma_one_frame(b: Seq<u8>, out: Seq<u8>)
    requires
        b.len() >= 5,
        le(b, 0, 4) == MAGIC,
        frame(b, 0) == Some((b.len() as int, out)),
    ensures
        decompress(b) == Some(out),
{
    assert(!skippable(MAGIC));
    assert(Seq::<u8>::empty() + out =~= out);
    reveal_with_fuel(frames_d, 2);
}

/// The decoder's output after a block it accepted starts with what it had.
proof fn lemma_step_prefix(u: Seq<u8>, w: nat, st: FrameState)
    ensures
        block_step(u, 0, w, w, st) is Some ==> prefix(st.out, block_step(u, 0, w, w, st).unwrap().1.out),
{
    crate::stream::lemma_block_step_prefix(u, 0, w, w, st);
}

/// `o2` is `o1` and one more block, which steps from `cur` to `nxt`.
pub open spec fn stepped(o1: Seq<u8>, o2: Seq<u8>, w: nat, cur: FrameState, nxt: FrameState, last: bool) -> bool {
    let u = o2.subrange(o1.len() as int, o2.len() as int);
    &&& o1.len() + 3 <= o2.len()
    &&& o2.subrange(0, o1.len() as int) == o1
    &&& 3 + body_len(u) <= u.len()
    &&& block_step(u, 0, w, w, cur) == Some((u.len() as int, nxt, last))
}

/// A raw block of `src[pos..end]`.
fn raw_block(out: &mut Vec<u8>, src: &[u8], pos: usize, end: usize, last: bool, Ghost(w): Ghost<nat>, Ghost(cur): Ghost<FrameState>)
    requires
        pos <= end <= src@.len(),
        end - pos <= min(w as int, BLOCK_MAX as int),
    ensures
        stepped(old(out)@, final(out)@, w, cur, FrameState { out: cur.out + src@.subrange(pos as int, end as int), ..cur }, last),
{
    let ghost o1 = out@;
    let ghost data = src@.subrange(pos as int, end as int);
    put_block_header(out, end - pos, 0, last);
    let ghost oh = out@;
    out.extend_from_slice(slice_subrange(src, pos, end));
    proof {
        let u = out@.subrange(o1.len() as int, out@.len() as int);
        assert(oh.subrange(0, o1.len() as int) == o1);
        assert(out@.subrange(0, o1.len() as int) =~= o1);
        lemma_le_same(oh, out@, o1.len() as int, 3);
        assert(out@.subrange(o1.len() as int, o1.len() + 3int) =~= u.subrange(0, 3));
        lemma_le_local(out@, o1.len() as int, u, 0, 3);
        assert(u.subrange(3, u.len() as int) =~= data);
        lemma_raw_step(u, data, w, cur, last);
    }
}

/// An RLE block of `size` copies of `x`.
fn rle_block(out: &mut Vec<u8>, x: u8, size: usize, last: bool, Ghost(w): Ghost<nat>, Ghost(cur): Ghost<FrameState>)
    requires
        size <= min(w as int, BLOCK_MAX as int),
    ensures
        stepped(old(out)@, final(out)@, w, cur, FrameState { out: cur.out + Seq::new(size as nat, |k: int| x), ..cur }, last),
{
    let ghost o1 = out@;
    put_block_header(out, size, 1, last);
    let ghost oh = out@;
    out.push(x);
    proof {
        let u = out@.subrange(o1.len() as int, out@.len() as int);
        assert(oh.subrange(0, o1.len() as int) == o1);
        assert(out@.subrange(0, o1.len() as int) =~= o1);
        lemma_le_same(oh, out@, o1.len() as int, 3);
        assert(out@.subrange(o1.len() as int, o1.len() + 3int) =~= u.subrange(0, 3));
        lemma_le_local(out@, o1.len() as int, u, 0, 3);
        lemma_rle_step(u, x, size as nat, w, cur, last);
    }
}

/// A compressed block of `src[pos..end]` from the encoder, checked with
/// the verified decoder `d`. On `Some(st2)`: the block was added and `d`
/// decoded it to `st2`; on `None`, `out` is as it was, and `d` is still in
/// `cur` if the second value is true.
#[verifier::rlimit(40)]
fn comp_block(
    out: &mut Vec<u8>,
    enc: &mut Enc,
    d: &mut FrameDec,
    src: &[u8],
    pos: usize,
    end: usize,
    last: bool,
    window: u64,
    Ghost(cur): Ghost<FrameState>,
    Tracked(m): Tracked<&mut Meter>,
) -> (r: (bool, bool, Ghost<FrameState>))
    requires
        old(enc).wf(),
        pos < end <= src@.len(),
        end <= IN_MAX,
        end - pos <= min(window as int, BLOCK_MAX as int),
        dec_is(old(d), cur),
        old(d).fstart == 0,
        old(d).out@.len() == pos,
        cur.out == src@.subrange(0, pos as int),
    ensures
        final(enc).wf(),
        r.0 ==> stepped(old(out)@, final(out)@, window as nat, cur, r.2@, last),
        r.0 ==> r.2@.out == src@.subrange(0, end as int),
        r.0 ==> dec_is(final(d), r.2@) && final(d).fstart == 0 && final(d).out@.len() == end,
        !r.0 ==> final(out)@ == old(out)@,
        !r.0 && r.1 ==> *final(d) == *old(d),
{
    let ghost w = window as nat;
    let ghost o1 = out@;
    let at = out.len();
    let size = end - pos;
    put_block_header(out, 0, 2, last);
    let ok = enc.block(src, pos, end, d.r1, d.r2, d.r3, out);
    let blen = out.len() - at;
    if !ok || blen < 4 || blen - 3 >= size {
        out.truncate(at);
        proof {
            assert(out@ =~= o1);
        }
        return (false, true, Ghost(cur));
    }
    // The block header, now that the size is known.
    let bsize = blen - 3;
    let l: u64 = if last {
        1
    } else {
        0
    };
    let bh: u64 = (bsize as u64) * 8 + 4 + l;
    out.set(at, (bh % 256) as u8);
    out.set(at + 1, ((bh / 256) % 256) as u8);
    out.set(at + 2, ((bh / 65536) % 256) as u8);
    proof {
        assert(out@.subrange(0, at as int) =~= o1);
    }
    let olimit = end;
    let ghost dout0 = d.out@;
    let u = slice_subrange(out.as_slice(), at, out.len());
    let (res, j, lst) = block_exec(u, 0, window, window, d, olimit, Ghost(cur), Tracked(m));
    let good = match res {
        Step::Done => j == u.len() && lst == last && d.out.len() == end && same(d.out.as_slice(), pos, src, pos, size),
        _ => false,
    };
    if !good {
        out.truncate(at);
        proof {
            assert(out@ =~= o1);
        }
        return (false, false, Ghost(cur));
    }
    let ghost st2 = block_step(u@, 0, w, w, cur).unwrap().1;
    proof {
        let uu = u@;
        assert(out@.subrange(at as int, out@.len() as int) == uu);
        let bs = block_step(uu, 0, w, w, cur);
        assert(bs is Some);
        let (jj, s2, l2) = bs.unwrap();
        assert(jj == uu.len());
        assert(l2 == last);
        assert(dec_is(d, s2));
        assert(fout(d.out@, 0) =~= d.out@);
        lemma_step_prefix(uu, w, cur);
        assert(d.out@ =~= d.out@.subrange(0, pos as int) + d.out@.subrange(pos as int, end as int));
        assert(src@.subrange(0, end as int) =~= src@.subrange(0, pos as int) + src@.subrange(pos as int, end as int));
        assert(s2.out =~= src@.subrange(0, end as int));
        assert(3 + body_len(uu) <= uu.len());
    }
    (true, false, Ghost(st2))
}

/// Compresses `src` into one frame.
#[verifier::rlimit(60)]
pub fn compress_exec(src: &[u8], p: Params) -> (r: Vec<u8>)
    requires
        src@.len() <= IN_MAX,
        10 <= p.wlog <= 31,
    ensures
        decompress(r@) == Some(src@),
{
    let n = src.len();
    let mut out: Vec<u8> = Vec::with_capacity(n / 2 + 64);
    proof {
        assert(pow2(32) == 0x1_0000_0000) by {
            lemma2_to64();
        }
    }
    push_le(&mut out, 0xFD2FB528, 4);
    let ghost o0 = out@;
    proof {
        lemma_pow2_le(p.wlog as nat, 31);
        lemma_pow2_le(10, p.wlog as nat);
        lemma_u64_pow2_no_overflow(p.wlog as nat);
        lemma_u64_shl_is_mul(1, p.wlog as u64);
        assert(pow2(31) == 0x8000_0000 && pow2(10) == 1024) by {
            lemma2_to64();
        }
    }
    let wmax: u64 = 1u64 << p.wlog;
    let single = (n as u64) <= wmax;
    let (window, hsize) = put_header(&mut out, n as u64, single, p.wlog, p.checksum);
    let ghost hdr = Header { window: window as nat, fcs: Some(n as nat), checksum: p.checksum, dict_id: 0, size: hsize as int };
    let ghost w = window as nat;
    let ghost hb = out@;
    let h0 = out.len();
    proof {
        assert(out@.subrange(0, 4) =~= o0);
        lemma_le_same(o0, out@, 0, 4);
        assert(chain(out@, h0 as int, w, initial_state()));
        assert(out@.subrange(0, h0 as int) =~= hb);
        assert(hb.subrange(4, h0 as int) == out@.subrange(4, out@.len() as int));
    }
    // The largest block: 128 KiB, or the window if smaller.
    let bmax: usize = if window < 131072 {
        window as usize
    } else {
        131072
    };
    let mut enc = Enc::new(src, window, p.level);
    let mut d = FrameDec { out: Vec::new(), fstart: 0, r1: 1, r2: 4, r3: 8, huf: None, seqt: None, lits: Vec::new() };
    let mut valid = true;
    let ghost mut cur = initial_state();
    let ghost mut fin = initial_state();
    let mut pos: usize = 0;
    let tracked mut m = Meter { n: 0 };
    proof {
        assert(d.out@ =~= Seq::<u8>::empty());
        assert(src@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(fout(d.out@, 0) =~= Seq::<u8>::empty());
        assert(huf_opt_is(d.huf, None));
        assert(seqt_opt_is(d.seqt, None));
        assert(dec_is(&d, cur));
    }
    loop
        invariant_except_break
            pos <= n,
            chain(out@, h0 as int, w, cur),
            cur.out == src@.subrange(0, pos as int),
            valid ==> dec_is(&d, cur) && d.fstart == 0 && d.out@.len() == pos,
        invariant
            n == src@.len(),
            n <= IN_MAX,
            bmax as int == min(w as int, BLOCK_MAX as int),
            w == window as nat,
            single ==> window == n,
            !single ==> window < n,
            bmax >= 1 || n == 0,
            h0 <= out@.len(),
            out@.subrange(0, h0 as int) == hb,
            frame_header(hb.subrange(4, h0 as int)) == Some(hdr),
            hdr == (Header { window: window as nat, fcs: Some(n as nat), checksum: p.checksum, dict_id: 0, size: hsize as int }),
            h0 == 4 + hsize,
            hsize <= 14,
            hb.len() == h0,
            le(hb, 0, 4) == MAGIC,
            enc.wf(),
        ensures
            forall|t: Seq<u8>| #[trigger] blocks_r(out@ + t, h0 as int, w, w, initial_state()) == Some((out@.len() as int, fin)),
            fin.out == src@,
        decreases n - pos,
    {
        let rest = n - pos;
        let size = if rest < bmax {
            rest
        } else {
            bmax
        };
        let end = pos + size;
        let last = end == n;
        let ghost o1 = out@;
        let ghost data = src@.subrange(pos as int, end as int);
        let ghost nxt = FrameState { out: cur.out + data, ..cur };
        let ghost mut s2 = nxt;
        proof {
            assert(nxt.out =~= src@.subrange(0, end as int));
        }
        let mut done = false;
        if size >= 2 && all_eq(src, pos, end, src[pos]) {
            let x = src[pos];
            rle_block(&mut out, x, size, last, Ghost(w), Ghost(cur));
            proof {
                assert(Seq::new(size as nat, |k: int| x) =~= data);
            }
            if valid {
                d.out.extend_from_slice(slice_subrange(src, pos, end));
                proof {
                    assert(fout(d.out@, 0) =~= nxt.out);
                }
            }
            done = true;
        } else if valid && size >= 16 {
            let (ok, still, Ghost(st2)) = comp_block(&mut out, &mut enc, &mut d, src, pos, end, last, window, Ghost(cur), Tracked(&mut m));
            if ok {
                proof {
                    s2 = st2;
                }
                done = true;
            } else if !still {
                valid = false;
            }
        }
        if !done {
            raw_block(&mut out, src, pos, end, last, Ghost(w), Ghost(cur));
            if valid {
                d.out.extend_from_slice(slice_subrange(src, pos, end));
                proof {
                    assert(fout(d.out@, 0) =~= nxt.out);
                }
            }
        }
        proof {
            let u = out@.subrange(o1.len() as int, out@.len() as int);
            assert(o1 + u =~= out@);
            assert(out@.subrange(0, h0 as int) =~= hb) by {
                assert(o1.subrange(0, h0 as int) == hb);
                assert(out@.subrange(0, h0 as int) =~= o1.subrange(0, h0 as int));
            }
            assert(s2.out == src@.subrange(0, end as int));
            if last {
                assert forall|t: Seq<u8>| #[trigger] blocks_r(out@ + t, h0 as int, w, w, initial_state()) == Some((out@.len() as int, s2)) by {
                    lemma_chain_last(o1, u, h0 as int, w, cur, s2, t);
                    assert(o1 + u == out@);
                }
                fin = s2;
                assert(src@.subrange(0, n as int) =~= src@);
            } else {
                lemma_chain_step(o1, u, h0 as int, w, cur, s2);
            }
        }
        if last {
            break;
        }
        proof {
            cur = s2;
        }
        pos = end;
    }
    let ghost ob = out@;
    let ghost jb = out@.len() as int;
    if p.checksum {
        let x = verilith_xxhash::xxh64::xxh64_exec(src);
        let lo = x & 0xFFFF_FFFF;
        proof {
            assert(x & 0xFFFF_FFFF == x % 0x1_0000_0000) by (bit_vector);
            assert(lo <= 0xFFFF_FFFF) by (bit_vector)
                requires
                    lo == x & 0xFFFF_FFFF,
            ;
            assert(pow2(32) == 0x1_0000_0000) by {
                lemma2_to64();
            }
        }
        push_le(&mut out, lo, 4);
    }
    proof {
        let b = out@;
        let t = b.subrange(jb, b.len() as int);
        assert(ob + t =~= b);
        assert(blocks_r(b, h0 as int, w, w, initial_state()) == Some((jb, fin)));
        assert(b.subrange(0, h0 as int) == hb) by {
            assert(b.subrange(0, h0 as int) =~= ob.subrange(0, h0 as int));
        }
        lemma_le_same(hb, b, 0, 4);
        let a = hb.subrange(4, h0 as int);
        let bb = b.subrange(4, b.len() as int);
        assert(bb.subrange(0, a.len() as int) =~= a) by {
            assert(bb.subrange(0, a.len() as int) =~= b.subrange(0, h0 as int).subrange(4, h0 as int));
        }
        lemma_fh_ext(a, bb);
        assert(no_dict().st == initial_state());
        assert(fin.out.subrange(0, fin.out.len() as int) =~= src@);
        assert(frame(b, 0) == Some((b.len() as int, src@)));
        lemma_one_frame(b, src@);
    }
    out
}

/// Compresses `src` at a zstd compression `level` (1 to 22; lower is
/// faster, higher is smaller), with libzstd's window size for that level.
pub fn compress(src: &[u8], level: i32, checksum: bool) -> (r: Vec<u8>)
    requires
        src@.len() <= IN_MAX,
    ensures
        decompress(r@) == Some(src@),
{
    let lp = crate::enc::level_params(level);
    compress_exec(src, Params { wlog: lp.0, checksum, level })
}

} // verus!
