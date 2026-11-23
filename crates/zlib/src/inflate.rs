//! The DEFLATE decoder, proven to compute `spec::inflate_blocks`.
//!
//! `Inflater::run` decodes into a caller-provided output buffer and can stop
//! when the buffer is full, keeping its state, so the caller can grow the
//! buffer and continue. Within a block it first runs a fast loop that needs
//! no input or output checks per symbol (at least 8 input bytes and
//! `FAST_OUT_MARGIN` output bytes remain), then a careful loop for the tail.
use crate::huffman::*;
#[cfg(verus_only)]
use verilith_core::huffman::*;
#[cfg(verus_only)]
use crate::ilemmas::*;
#[cfg(verus_only)]
use crate::slemmas::{lemma_after_pos, lemma_blocks_hdr_past, lemma_codes_first, lemma_stored_rest_past, lemma_read_dynamic_end, lemma_read_lens_step, lemma_rest_pos, rep_bits};
#[cfg(verus_only)]
use verilith_core::bits::*;
use verilith_core::prims::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

/// Room the fast loop needs per iteration: a match is copied 8 bytes at a
/// time, at least 40 bytes when its distance is at least 8, so it may
/// write up to 40 bytes past its end.
pub const FAST_OUT_MARGIN: usize = 258 + 40;

// Work. `Inflater::work` counts the iterations of every loop the decoder
// runs (in this file and in `huffman`); copies done by a primitive count one
// per byte. The constants bound the parts.

/// Loads into the bit buffer.
pub open spec fn refill_cost() -> nat {
    7
}

/// Looks up a symbol (`peek`, `decode_careful`).
pub open spec fn peek_cost() -> nat {
    22
}

/// Builds the fixed code's tables.
pub open spec fn fixed_cost() -> nat {
    10834
}

/// Reads a dynamic header and builds its tables.
pub open spec fn dynamic_cost() -> nat {
    21200
}

/// Reads any block header.
pub open spec fn header_cost() -> nat {
    refill_cost() + dynamic_cost()
}

/// One step of the careful loop, besides the bytes it copies.
pub open spec fn step_cost() -> nat {
    50
}

/// One iteration of the fast loop.
pub open spec fn iter_cost() -> nat {
    72
}

/// The constant part of decoding a block body (one call of `codes` or
/// `stored`); the rest is `iter_cost()` per bit read and one per byte
/// written.
pub open spec fn body_cost() -> nat {
    130
}

/// The most a call that stops for more input can spend on the unit (block
/// header or symbol) it then rolls back: work not paid for by the input
/// before that unit.
pub open spec fn fail_cost() -> nat {
    header_cost() + fixed_cost() + body_cost()
}

/// Work per input bit, enough to pay for every block header.
pub open spec fn bit_cost() -> nat {
    1200
}

/// Work the decoder has been paid for but not done yet: the fixed tables
/// to rebuild, and the end of the current block body.
pub open spec fn credit(fixed: bool, mode: u8) -> nat {
    fixed_credit(fixed) + if mode == MODE_STORED || mode == MODE_CODES {
        body_cost()
    } else {
        0
    }
}

/// The fixed tables still to rebuild.
pub open spec fn fixed_credit(fixed: bool) -> nat {
    if fixed {
        0
    } else {
        fixed_cost()
    }
}

/// `x` (the input the decoder is given) is the start of `b` (the whole
/// stream, which may continue past it). The decoder is proven against `b`:
/// it only reads `x`, and when `x` ends early it stops at a point from which
/// decoding can resume once more of `b` arrives.
pub open spec fn prefix(x: Seq<u8>, b: Seq<u8>) -> bool {
    x.len() <= b.len() && x == b.subrange(0, x.len() as int)
}

/// A byte of the given input is that byte of the whole stream.
pub proof fn lemma_prefix_index(x: Seq<u8>, b: Seq<u8>, i: int)
    requires
        prefix(x, b),
        0 <= i < x.len(),
    ensures
        x[i] == b[i],
{
    assert(x[i] == b.subrange(0, x.len() as int)[i]);
}

/// So is a little-endian word read from it.
pub proof fn lemma_prefix_le(x: Seq<u8>, b: Seq<u8>, i: int, n: nat)
    requires
        prefix(x, b),
        0 <= i,
        i + n <= x.len(),
    ensures
        le_bytes(x, i, n) == le_bytes(b, i, n),
    decreases n,
{
    if n > 0 {
        lemma_prefix_index(x, b, i);
        lemma_prefix_le(x, b, i + 1, (n - 1) as nat);
    }
}

/// The order in which the code length code's lengths are sent.
pub const CLEN_ORDER: [u8; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

pub const MODE_HEADER: u8 = 0;

pub const MODE_STORED: u8 = 1;

pub const MODE_CODES: u8 = 2;

pub const MODE_DONE: u8 = 3;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum Status {
    /// The final block has been decoded.
    Done,
    /// The output buffer is full; grow it and call `run` again.
    NeedOutput,
    /// The input is malformed.
    BadData,
    /// The input ends before the stream does. The state is at a point
    /// where decoding can continue: bytes from `in_pos` on are not used
    /// yet, and `run` can be called again with them followed by more input.
    Truncated,
}

#[derive(Clone)]
pub struct Inflater {
    pub lit: [u32; LIT_SIZE],
    pub dist: [u32; DIST_SIZE],
    pub cl: [u32; CL_SIZE],
    pub lit_code: Code,
    pub dist_code: Code,
    pub cl_code: Code,
    pub lens: [u8; 320],
    /// The tables hold the fixed code.
    pub fixed: bool,
    /// Bit reader: `cnt` bits of `buf` are the input bits just before byte
    /// `in_pos`; the bits above them are zero.
    pub buf: u64,
    pub cnt: u32,
    pub in_pos: usize,
    pub out_pos: usize,
    pub mode: u8,
    /// The current block is the final one.
    pub last: bool,
    /// Bytes of the current stored block not yet copied.
    pub stored_left: usize,
    /// A match not yet fully copied.
    pub copy_len: usize,
    pub copy_dist: usize,
    /// The code lengths the literal/length and distance tables were built
    /// from.
    pub lit_lens: Ghost<Seq<u8>>,
    pub dist_lens: Ghost<Seq<u8>>,
    /// Loop iterations run so far.
    pub work: Ghost<nat>,
}

/// The value of entry `e` given the bit buffer before its bits were
/// consumed: the literal or symbol, or the base plus the extra bits.
#[inline(always)]
fn value(e: u32, saved: u64) -> (r: u32)
    requires
        e & 0xff < 64,
        (e >> 8u32) & 0x1f <= e & 0xff,
        (e & 0xff) - ((e >> 8u32) & 0x1f) <= 16,
    ensures
        r as nat == ((e >> 16u32) & 0x7fff) as nat + (saved as nat % pow2((e & 0xff) as nat)) / pow2(
            ((e >> 8u32) & 0x1f) as nat,
        ),
{
    let t = total_bits(e);
    let c = code_len(e);
    proof {
        lemma_and_mask(saved, t as u64);
        lemma_u64_shr_is_div(saved & lowmask(t as u64), c as u64);
        lemma_pow2_pos(t as nat);
        vstd::arithmetic::div_mod::lemma_mod_bound(saved as int, pow2(t as nat) as int);
        lemma_div_pow2_bound(saved as nat % pow2(t as nat), t as nat, c as nat);
        lemma2_to64();
        if t - c < 16 {
            lemma_pow2_strictly_increases((t - c) as nat, 16);
        }
        assert((e >> 16u32) & 0x7fff <= 0x7fff) by (bit_vector);
    }
    ((e >> 16) & 0x7fff) + ((saved & mask(t)) >> (c as u64)) as u32
}

/// The low `n < 64` bits set.
#[inline(always)]
fn mask(n: u32) -> (r: u64)
    requires
        n < 64,
    ensures
        r == lowmask(n as u64),
        r as nat == pow2(n as nat) - 1,
{
    proof {
        lemma_mask(n as u64);
    }
    (1u64 << (n as u64)) - 1
}

/// Tops the fast loop's buffer up to 56..63 bits with one 8-byte load.
#[inline(always)]
fn fast_refill(input: &[u8], Ghost(b): Ghost<Seq<u8>>, buf: u64, cnt: u32, ip: usize, Ghost(a): Ghost<nat>) -> (r: (
    u64,
    u32,
    usize,
))
    requires
        prefix(input@, b),
        fast_bits(b, buf, cnt, ip as int, a),
        ip + 8 <= input@.len() <= usize::MAX,
    ensures
        fast_bits(b, r.0, r.1, r.2 as int, 64),
        8 * r.2 - r.1 == 8 * ip - cnt,
        r.1 >= 56,
        ip <= r.2 <= ip + 7,
{
    let w = load_u64_le(input, ip);
    proof {
        lemma_prefix_le(input@, b, ip as int, 8);
        lemma_fast_refill(b, buf, cnt, ip as int, a, w);
    }
    (buf | (w << (cnt as u64)), cnt | 56, ip + ((63 - cnt) >> 3) as usize)
}

/// Consumes the bits of entry `e` from the fast loop's buffer, returning
/// its value.
#[inline(always)]
fn fast_take(buf: u64, cnt: u32, e: u32, Ghost(b): Ghost<Seq<u8>>, Ghost(ip): Ghost<int>, Ghost(a): Ghost<
    nat,
>) -> (r: (u64, u32, u32))
    requires
        fast_bits(b, buf, cnt, ip, a),
        e & 0xff <= cnt,
        (e >> 8u32) & 0x1f <= e & 0xff,
        (e & 0xff) - ((e >> 8u32) & 0x1f) <= 16,
    ensures
        r.1 == cnt - (e & 0xff),
        fast_bits(b, r.0, r.1, ip, (a - (e & 0xff)) as nat),
        r.2 as nat == ((e >> 16u32) & 0x7fff) as nat + bits(
            b,
            8 * ip - cnt + ((e >> 8u32) & 0x1f),
            ((e & 0xff) - ((e >> 8u32) & 0x1f)) as nat,
        ),
{
    let t = total_bits(e);
    proof {
        lemma_shr_bits(b, 8 * ip - cnt, a, buf, t as u64);
        lemma_value_bits(b, 8 * ip - cnt, a, buf as nat, t as nat, ((e >> 8u32) & 0x1f) as nat);
    }
    // `e & 0x3f` is `t`, as `t < 64`; shifting by it lets the compiler use
    // the shift instruction's own 6-bit count, keeping a zero-extension off
    // the chain from one table lookup to the next.
    let sh = (e & 0x3f) as u64;
    proof {
        assert(e & 0xff < 64 ==> e & 0x3f == e & 0xff) by (bit_vector);
    }
    (buf >> sh, cnt - t, value(e, buf))
}

/// Copies the match of length `len` from `d` back to `op` with 8-byte moves.
/// It may write up to 40 bytes past the match: when `d >= 8` it always
/// writes the first 40 bytes, which covers most matches without a branch.
#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn copy_fast(out: &mut [u8], op: usize, d: usize, len: usize, Ghost(o): Ghost<Seq<u8>>) -> (w: Ghost<nat>)
    requires
        old(out)@.subrange(0, op as int) == o,
        1 <= d <= op,
        len <= 258,
        op + len + 40 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.subrange(0, op + len) == copy_match(o, d as nat, len as nat),
        w@ <= 40,
{
    let ghost mut w: nat = 0;
    // `c` is the match continued well past `len`: every write below puts
    // `c`'s bytes in place.
    let ghost c = copy_match(o, d as nat, 300);
    let n = out.len();
    proof {
        lemma_copy_match_index(o, d as nat, 300);
        assert forall|i: int| 0 <= i < op implies out@[i] == #[trigger] c[i] by {
            assert(c.subrange(0, op as int)[i] == c[i]);
            assert(out@.subrange(0, op as int)[i] == out@[i]);
        }
    }
    let src = op - d;
    if d >= 8 {
        let ghost o1 = out@;
        copy8(out, src, op);
        proof {
            lemma_copy8_ok(o1, out@, c, src as int, op as int);
        }
        let ghost o2 = out@;
        copy8(out, src + 8, op + 8);
        proof {
            lemma_copy8_ok(o2, out@, c, src + 8, op + 8);
        }
        let ghost o3 = out@;
        copy8(out, src + 16, op + 16);
        proof {
            lemma_copy8_ok(o3, out@, c, src + 16, op + 16);
        }
        let ghost o4 = out@;
        copy8(out, src + 24, op + 24);
        proof {
            lemma_copy8_ok(o4, out@, c, src + 24, op + 24);
        }
        let ghost o5 = out@;
        copy8(out, src + 32, op + 32);
        proof {
            lemma_copy8_ok(o5, out@, c, src + 32, op + 32);
        }
        let mut k: usize = 40;
        while k < len
            invariant
                40 <= k <= len + 7 || k == 40,
                len <= 258,
                8 <= d <= op,
                src == op - d,
                op + len + 16 <= out@.len(),
                out@.len() == n,
                out@.len() == old(out)@.len(),
                c.len() == op + 300,
                forall|i: int| op <= i < op + 300 ==> #[trigger] c[i] == c[i - d],
                forall|i: int| 0 <= i < op + k ==> out@[i] == #[trigger] c[i],
                8 * w + 40 == k,
            decreases len + 8 - k,
        {
            proof {
                w = w + 1;
            }
            let ghost o3 = out@;
            copy8(out, src + k, op + k);
            proof {
                lemma_copy8_ok(o3, out@, c, src + k, op + k);
            }
            k = k + 8;
        }
    } else if d == 1 {
        let v = get(out, src);
        proof {
            assert forall|i: int| op <= i < op + 300 implies #[trigger] c[i] == v by {
                lemma_run(c, op as int, i);
            }
        }
        let mut k: usize = 0;
        while k < len
            invariant
                k <= len + 7,
                len <= 258,
                d == 1,
                op + len + 16 <= out@.len(),
                out@.len() == n,
                out@.len() == old(out)@.len(),
                c.len() == op + 300,
                forall|i: int| op <= i < op + 300 ==> #[trigger] c[i] == v,
                forall|i: int| 0 <= i < op + k ==> out@[i] == #[trigger] c[i],
                8 * w == k,
            decreases len + 8 - k,
        {
            proof {
                w = w + 1;
            }
            let ghost o3 = out@;
            fill8(out, op + k, v);
            proof {
                assert forall|i: int| 0 <= i < op + k + 8 implies out@[i] == #[trigger] c[i] by {
                    if i >= op + k {
                        assert(out@[i] == v);
                    } else {
                        assert(out@[i] == o3[i]);
                    }
                }
            }
            k = k + 8;
        }
    } else {
        // Copy 8 bytes one at a time; from then on the output has
        // period `d`, so 8-byte copies from `dd` (the least multiple
        // of `d` that is at least 8) back are exact.
        let mut k: usize = 0;
        while k < 8
            invariant
                k <= 8,
                2 <= d < 8,
                d <= op,
                src == op - d,
                op + len + 16 <= out@.len(),
                out@.len() == n,
                out@.len() == old(out)@.len(),
                c.len() == op + 300,
                forall|i: int| op <= i < op + 300 ==> #[trigger] c[i] == c[i - d],
                forall|i: int| 0 <= i < op + k ==> out@[i] == #[trigger] c[i],
                w == k,
            decreases 8 - k,
        {
            proof {
                w = w + 1;
            }
            let v = get(out, src + k);
            set(out, op + k, v);
            proof {
                assert(c[op + k] == c[op + k - d]);
            }
            k = k + 1;
        }
        let dd = if d == 2 || d == 4 {
            8
        } else if d == 3 {
            9
        } else if d == 5 {
            10
        } else if d == 6 {
            12
        } else {
            14
        };
        let ghost m: nat = if d == 2 {
            4
        } else if d == 3 {
            3
        } else {
            2
        };
        proof {
            assert(dd == m * d && 8 <= dd && dd <= d + 7);
        }
        while k < len
            invariant
                8 <= k <= len + 7 || k == 8,
                len <= 258,
                2 <= d < 8,
                d <= op,
                dd == m * d,
                8 <= dd <= d + 7,
                8 * w == k + 56,
                op + len + 16 <= out@.len(),
                out@.len() == n,
                out@.len() == old(out)@.len(),
                c.len() == op + 300,
                forall|i: int| op <= i < op + 300 ==> #[trigger] c[i] == c[i - d],
                forall|i: int| 0 <= i < op + k ==> out@[i] == #[trigger] c[i],
            decreases len + 8 - k,
        {
            proof {
                w = w + 1;
            }
            let ghost o3 = out@;
            copy8(out, op + k - dd, op + k);
            proof {
                assert forall|i: int| op + k <= i < op + k + 8 implies #[trigger] c[i] == c[i - (op + k)
                    + (op + k - dd)] by {
                    assert(i - (m - 1) * d >= op) by (nonlinear_arith)
                        requires
                            dd == m * d,
                            dd <= d + 7,
                            i >= op + k,
                            k >= 8,
                    ;
                    lemma_period(c, d as int, op as int, m, i);
                }
                lemma_copy8_ok(o3, out@, c, op + k - dd, op + k);
            }
            k = k + 8;
        }
    }
    proof {
        lemma_copy_match_prefix(o, d as nat, len as nat, (300 - len) as nat);
        assert(len as nat + (300 - len) as nat == 300);
        assert(out@.subrange(0, op + len) =~= c.subrange(0, op + len));
    }
    Ghost(w)
}

/// How an iteration of the fast loop ended.
pub enum Fast {
    /// Decoded symbols; the new bit reader, output position and next entry.
    Next(u64, u32, usize, usize, u32, Ghost<nat>),
    /// The block ended; the bit reader after it.
    Eob(u64, u32, usize),
    /// The data is bad.
    Bad,
}

/// What looking up the symbol at bit `pos` with code lengths `lens` may
/// return, with `cnt` bits buffered from `pos`. `Truncated` says the input
/// ran out; only if it is `whole` stream does that mean the stream ends.
pub open spec fn peek_ok(r: Result<u32, Status>, b: Seq<u8>, pos: int, lens: Seq<u8>, which: u8, cnt: nat, whole: bool) -> bool {
    match r {
        Ok(e) => match decode(lens, b, pos) {
            Some((s, k)) => e == ent(which, s, k) && k + extra_of(which, s) <= cnt && s < lens.len()
                && 1 <= k <= 15,
            None => false,
        },
        Err(st) => {
            ||| st == Status::BadData && decode(lens, b, pos) is None
            ||| st == Status::Truncated && (whole ==> match decode(lens, b, pos) {
                None => true,
                Some((s, k)) => pos + k + extra_of(which, s) > nbits(b),
            })
        },
    }
}

/// The tables hold the fixed code, if `fixed`. Opaque, so that the 288
/// fixed lengths stay out of proofs that do not need them.
#[verifier::opaque]
pub open spec fn fixed_tables(
    fixed: bool,
    lit: [u32; LIT_SIZE],
    lit_code: Code,
    dist: [u32; DIST_SIZE],
    dist_code: Code,
) -> bool {
    fixed ==> {
        &&& table_ok(lit@, fixed_lit_lens(), 11, ALPHA_LIT)
        &&& code_ok(lit_code, fixed_lit_lens())
        &&& table_ok(dist@, fixed_dist_lens(), 8, ALPHA_DIST)
        &&& code_ok(dist_code, fixed_dist_lens())
    }
}

/// `rest` in each mode. (Separate lemmas, so that proofs about one mode do
/// not see `inflate_blocks`.)
pub proof fn lemma_rest_header(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.mode == MODE_HEADER,
    ensures
        s.rest(b, o) == after(b, s.last, Some((s.pos(), o))),
{
    reveal(Inflater::rest);
    reveal(after);
}

pub proof fn lemma_rest_stored(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.mode == MODE_STORED,
    ensures
        s.rest(b, o) == after(b, s.last, stored_rest(b, s.pos(), s.stored_left as nat, o)),
{
    reveal(Inflater::rest);
}

pub proof fn lemma_rest_codes(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.mode == MODE_CODES,
    ensures
        s.rest(b, o) == after(
            b,
            s.last,
            inflate_codes(
                b,
                s.pos(),
                copy_match(o, s.copy_dist as nat, s.copy_len as nat),
                s.lit_lens@,
                s.dist_lens@,
            ),
        ),
{
    reveal(Inflater::rest);
}

/// `rest` depends on the bit reader only through the position.
pub proof fn lemma_rest_same(s1: Inflater, s2: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s1.pos() == s2.pos(),
        s1.same_but_bits(&s2),
    ensures
        s1.rest(b, o) == s2.rest(b, o),
{
    reveal(Inflater::rest);
}

/// A fresh stream's rest is all of `inflate_blocks`.
pub proof fn lemma_rest_start(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.mode == MODE_HEADER,
        !s.last,
    ensures
        s.rest(b, o) == inflate_blocks(b, s.pos(), o),
{
    reveal(Inflater::rest);
}

pub proof fn lemma_rest_done(s: Inflater, b: Seq<u8>, o: Seq<u8>)
    requires
        s.mode == MODE_DONE || (s.mode == MODE_HEADER && s.last),
    ensures
        s.rest(b, o) == Some((s.pos(), o)),
{
    reveal(Inflater::rest);
}

/// A result of decoding, if there is one, ends past bit `n`: the input
/// that ends there is too short for it.
pub open spec fn past(r: Option<(int, Seq<u8>)>, n: int) -> bool {
    r matches Some((e, _)) ==> e > n
}

impl Inflater {
    /// The bit position in the input the decoder has reached.
    pub open spec fn pos(&self) -> int {
        8 * self.in_pos - self.cnt
    }

    /// The bit buffer holds the `cnt` input bits from `pos` (and zeros
    /// above them), and the input up to `in_pos` has been read.
    pub open spec fn bits_ok(&self, b: Seq<u8>) -> bool {
        &&& self.cnt <= 63
        &&& self.in_pos <= b.len()
        &&& self.cnt <= 8 * self.in_pos
        &&& self.buf as nat == bits(b, self.pos(), self.cnt as nat)
    }

    /// Everything but the bit reader is as in `o`.
    pub open spec fn same_but_bits(&self, o: &Inflater) -> bool {
        &&& self.lit == o.lit
        &&& self.dist == o.dist
        &&& self.cl == o.cl
        &&& self.lit_code == o.lit_code
        &&& self.dist_code == o.dist_code
        &&& self.cl_code == o.cl_code
        &&& self.lens == o.lens
        &&& self.fixed == o.fixed
        &&& self.out_pos == o.out_pos
        &&& self.mode == o.mode
        &&& self.last == o.last
        &&& self.stored_left == o.stored_left
        &&& self.copy_len == o.copy_len
        &&& self.copy_dist == o.copy_dist
        &&& self.lit_lens == o.lit_lens
        &&& self.dist_lens == o.dist_lens
    }

    pub fn new() -> (r: Box<Inflater>)
        ensures
            r.fixed_ok(),
            r.work@ == 0,
    {
        proof {
            reveal(fixed_tables);
        }
        Box::new(
            Inflater {
                lit: [0; LIT_SIZE],
                dist: [0; DIST_SIZE],
                cl: [0; CL_SIZE],
                lit_code: Code::new(),
                dist_code: Code::new(),
                cl_code: Code::new(),
                lens: [0; 320],
                fixed: false,
                buf: 0,
                cnt: 0,
                in_pos: 0,
                out_pos: 0,
                mode: MODE_HEADER,
                last: false,
                stored_left: 0,
                copy_len: 0,
                copy_dist: 0,
                lit_lens: Ghost(Seq::empty()),
                dist_lens: Ghost(Seq::empty()),
                work: Ghost(0),
            },
        )
    }

    /// Starts a new stream at byte `start` of the input.
    pub fn reset(&mut self, start: usize)
        ensures
            final(self).buf == 0,
            final(self).cnt == 0,
            final(self).in_pos == start,
            final(self).out_pos == 0,
            final(self).mode == MODE_HEADER,
            !final(self).last,
            final(self).stored_left == 0,
            final(self).copy_len == 0,
            final(self).fixed_ok() == old(self).fixed_ok(),
            final(self).fixed == old(self).fixed,
            final(self).work == old(self).work,
    {
        self.buf = 0;
        self.cnt = 0;
        self.in_pos = start;
        self.out_pos = 0;
        self.mode = MODE_HEADER;
        self.last = false;
        self.stored_left = 0;
        self.copy_len = 0;
        self.copy_dist = 0;
    }

    /// The final block has been decoded.
    /// Gives back the whole bytes in the bit buffer, leaving fewer than 8
    /// bits: the input position becomes the first byte not yet touched.
    pub fn drop_whole_bytes(&mut self, Ghost(b): Ghost<Seq<u8>>)
        requires
            old(self).bits_ok(b),
        ensures
            final(self).bits_ok(b),
            final(self).cnt < 8,
            final(self).pos() == old(self).pos(),
            final(self).in_pos == old(self).in_pos - old(self).cnt / 8,
            final(self).same_but_bits(old(self)),
            final(self).work == old(self).work,
            old(self).inv(b) ==> final(self).inv(b),
    {
        let k = self.cnt / 8;
        let c = self.cnt - 8 * k;
        proof {
            lemma_shr_bits(b, self.pos(), self.cnt as nat, self.buf, c as u64);
        }
        self.buf = self.buf & mask(c);
        self.cnt = c;
        self.in_pos = self.in_pos - k as usize;
    }

    pub fn done(&self) -> (r: bool)
        ensures
            r == (self.mode == MODE_DONE),
    {
        self.mode == MODE_DONE
    }

    /// Input bytes consumed so far, counting a partly used byte.
    pub fn consumed(&self) -> (r: usize)
        requires
            self.cnt <= 8 * self.in_pos,
        ensures
            r as int == (self.pos() + 7) / 8,
    {
        proof {
            let q = self.cnt as int / 8;
            let r = self.cnt as int % 8;
            assert(self.pos() + 7 == 8 * (self.in_pos - q) + (7 - r));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                self.pos() + 7,
                8,
                self.in_pos - q,
                7 - r,
            );
        }
        self.in_pos - (self.cnt / 8) as usize
    }

    /// Loads input bytes until at least 56 bits (and at most 63) are
    /// buffered or the input is exhausted.
    #[inline(always)]
    fn refill(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).bits_ok(b),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).bits_ok(b),
            final(self).pos() == old(self).pos(),
            final(self).same_but_bits(old(self)),
            final(self).cnt >= old(self).cnt,
            final(self).cnt >= 56 || final(self).in_pos == input@.len(),
            final(self).work@ <= old(self).work@ + refill_cost(),
    {
        while self.cnt < 56 && self.in_pos < input.len()
            invariant
                self.bits_ok(b),
                self.pos() == old(self).pos(),
                self.same_but_bits(old(self)),
                self.cnt >= old(self).cnt,
                8 * self.work@ + old(self).cnt == 8 * old(self).work@ + self.cnt,
                prefix(input@, b),
                self.in_pos <= input@.len(),
            decreases input@.len() - self.in_pos,
        {
            self.work = Ghost(self.work@ + 1);
            proof {
                lemma_prefix_index(input@, b, self.in_pos as int);
                lemma_bits_bound(b, self.pos(), self.cnt as nat);
                lemma_or_byte(self.buf, b[self.in_pos as int] as u64, self.cnt as u64);
                lemma_bits_split(b, self.pos(), self.cnt as nat, 8);
                lemma_bits_byte(b, self.in_pos as int);
                assert(self.pos() + self.cnt == 8 * self.in_pos);
            }
            self.buf = self.buf | ((input[self.in_pos] as u64) << (self.cnt as u64));
            self.in_pos = self.in_pos + 1;
            self.cnt = self.cnt + 8;
        }
    }

    /// Takes `n <= 32` bits, or returns `None` if the input ends first.
    fn take(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, n: u32) -> (r: Option<u32>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).bits_ok(b),
            n <= 32,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).bits_ok(b),
            final(self).same_but_bits(old(self)),
            match r {
                Some(v) => v as nat == bits(b, old(self).pos(), n as nat) && final(self).pos() == old(
                    self,
                ).pos() + n,
                None => old(self).pos() + n > nbits(input@) && final(self).pos() == old(self).pos()
                    && final(self).in_pos == input@.len(),
            },
            final(self).work@ <= old(self).work@ + refill_cost(),
    {
        if self.cnt < n {
            self.refill(input, Ghost(b));
            if self.cnt < n {
                return None;
            }
        }
        proof {
            lemma_shr_bits(b, self.pos(), self.cnt as nat, self.buf, n as u64);
            lemma_bits_bound(b, self.pos(), n as nat);
            lemma2_to64();
            if n < 32 {
                lemma_pow2_strictly_increases(n as nat, 32);
            }
        }
        let v = (self.buf & mask(n)) as u32;
        self.buf = self.buf >> (n as u64);
        self.cnt = self.cnt - n;
        Some(v)
    }

    /// The tables for alphabet `which` decode the code with lengths `lens`.
    pub open spec fn table_for(&self, which: u8, lens: Seq<u8>) -> bool {
        if which == ALPHA_LIT {
            table_ok(self.lit@, lens, 11, ALPHA_LIT) && code_ok(self.lit_code, lens)
        } else if which == ALPHA_DIST {
            table_ok(self.dist@, lens, 8, ALPHA_DIST) && code_ok(self.dist_code, lens)
        } else {
            &&& which == ALPHA_CL
            &&& table_ok(self.cl@, lens, 7, ALPHA_CL)
            &&& code_ok(self.cl_code, lens)
            &&& lens.len() <= 19
        }
    }

    /// Looks up the next symbol with a table without consuming it.
    fn peek(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, which: u8, Ghost(lens): Ghost<Seq<u8>>) -> (r: Result<u32, Status>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).bits_ok(b),
            old(self).table_for(which, lens),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).bits_ok(b),
            final(self).pos() == old(self).pos(),
            final(self).same_but_bits(old(self)),
            peek_ok(r, b, old(self).pos(), lens, which, final(self).cnt as nat, input@ == b),
            r == Err::<u32, Status>(Status::Truncated) ==> final(self).in_pos == input@.len(),
            r == Err::<u32, Status>(Status::Truncated) ==> (decode(lens, b, old(self).pos()) matches Some((s, k))
                ==> old(self).pos() + k + extra_of(which, s) > nbits(input@)),
            final(self).work@ <= old(self).work@ + peek_cost(),
    {
        self.refill(input, Ghost(b));
        let ghost pos = self.pos();
        let ghost x = self.buf as nat;
        proof {
            // Seen from the input alone, which ends here when it is used up.
            if pos + self.cnt == nbits(input@) {
                crate::slemmas::lemma_prefix_bits(input@, b, pos, self.cnt as nat);
                lemma_decode_num(lens, input@, pos, self.cnt as nat, self.cnt as nat, 1);
            }
        }
        let ghost t: nat = if which == ALPHA_LIT {
            11
        } else if which == ALPHA_DIST {
            8
        } else {
            7
        };
        proof {
            lemma_and_mask(self.buf, t as u64);
            lemma_pow2_pos(t);
            vstd::arithmetic::div_mod::lemma_mod_bound(x as int, pow2(t) as int);
            lemma2_to64();
            if self.cnt >= MAX_BITS || pos + self.cnt == nbits(b) {
                lemma_decode_num(lens, b, pos, self.cnt as nat, self.cnt as nat, 1);
            } else if decode_num(lens, x, self.cnt as nat, 1) is Some {
                lemma_decode_num_some(lens, b, pos, self.cnt as nat, self.cnt as nat, 1);
            }
            lemma_decode_num_trunc(lens, x, self.cnt as nat, t, 1);
            lemma_decode_num_sym(lens, x % pow2(t), t, 1);
            lemma_decode_num_sym(lens, x, self.cnt as nat, 1);
            lemma_long();
        }
        let mut e = if which == ALPHA_LIT {
            self.lit[(self.buf & mask(LIT_BITS)) as usize]
        } else if which == ALPHA_DIST {
            self.dist[(self.buf & mask(DIST_BITS)) as usize]
        } else {
            self.cl[(self.buf & mask(CL_BITS)) as usize]
        };
        proof {
            let idx = (x % pow2(t)) as int;
            if which == ALPHA_LIT {
                assert(e == self.lit@[idx]);
            } else if which == ALPHA_DIST {
                assert(e == self.dist@[idx]);
            } else {
                assert(e == self.cl@[idx]);
            }
            assert(e == tab_entry(lens, which, x % pow2(t), t));
            if let Some((s, k)) = decode_num(lens, x % pow2(t), t, 1) {
                lemma_ent(which, s, k);
            }
        }
        if e & F_LONG != 0 {
            let code = if which == ALPHA_LIT {
                &self.lit_code
            } else if which == ALPHA_DIST {
                &self.dist_code
            } else {
                &self.cl_code
            };
            let (slow, Ghost(sw)) = decode_slow(code, which, self.buf, self.cnt, Ghost(lens));
            self.work = Ghost(self.work@ + sw);
            match slow {
                Some(x) => e = x,
                None => {
                    proof {
                        if self.cnt < 15 && self.in_pos == input@.len() {
                            crate::slemmas::lemma_decode_past(lens, input@, b, pos, which);
                        }
                    }
                    return Err(
                        if self.cnt >= 15 {
                            Status::BadData
                        } else {
                            Status::Truncated
                        },
                    )
                },
            }
            proof {
                if let Some((s, k)) = decode_num(lens, x, self.cnt as nat, 1) {
                    lemma_ent(which, s, k);
                }
            }
        }
        if total_bits(e) > self.cnt {
            proof {
                if self.in_pos == input@.len() {
                    crate::slemmas::lemma_decode_past(lens, input@, b, pos, which);
                }
            }
            return Err(Status::Truncated);
        }
        Ok(e)
    }

    /// Consumes the bits of entry `e` (code and extra bits), returning its
    /// value.
    #[inline(always)]
    fn consume(&mut self, e: u32, Ghost(b): Ghost<Seq<u8>>) -> (v: u32)
        requires
            old(self).bits_ok(b),
            e & 0xff <= old(self).cnt,
            (e >> 8u32) & 0x1f <= e & 0xff,
            (e & 0xff) - ((e >> 8u32) & 0x1f) <= 16,
        ensures
            final(self).in_pos == old(self).in_pos,
            final(self).bits_ok(b),
            final(self).same_but_bits(old(self)),
            final(self).pos() == old(self).pos() + (e & 0xff),
            final(self).work == old(self).work,
            v as nat == ((e >> 16u32) & 0x7fff) as nat + bits(
                b,
                old(self).pos() + ((e >> 8u32) & 0x1f),
                ((e & 0xff) - ((e >> 8u32) & 0x1f)) as nat,
            ),
    {
        let saved = self.buf;
        let t = total_bits(e);
        proof {
            lemma_shr_bits(b, self.pos(), self.cnt as nat, self.buf, t as u64);
            lemma_value_bits(
                b,
                self.pos(),
                self.cnt as nat,
                saved as nat,
                t as nat,
                ((e >> 8u32) & 0x1f) as nat,
            );
        }
        self.buf = self.buf >> (t as u64);
        self.cnt = self.cnt - t;
        value(e, saved)
    }

    /// Decodes one symbol, returning its entry with its code consumed.
    fn decode_careful(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, which: u8, Ghost(lens): Ghost<Seq<u8>>) -> (r: Result<
        u32,
        Status,
    >)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).bits_ok(b),
            old(self).table_for(which, lens),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).bits_ok(b),
            final(self).same_but_bits(old(self)),
            peek_ok(r, b, old(self).pos(), lens, which, old(self).cnt as nat + 64, input@ == b),
            r == Err::<u32, Status>(Status::Truncated) ==> final(self).in_pos == input@.len() && final(self).pos() == old(self).pos(),
            r == Err::<u32, Status>(Status::Truncated) ==> (decode(lens, b, old(self).pos()) matches Some((s, k))
                ==> old(self).pos() + k + extra_of(which, s) > nbits(input@)),
            r is Ok ==> final(self).pos() == old(self).pos() + (r->Ok_0 & 0xff),
            final(self).work@ <= old(self).work@ + peek_cost(),
    {
        let e = match self.peek(input, Ghost(b), which, Ghost(lens)) {
            Ok(e) => e,
            Err(s) => return Err(s),
        };
        proof {
            let (s, k) = decode(lens, b, old(self).pos())->Some_0;
            lemma_ent(which, s, k);
        }
        let _ = self.consume(e, Ghost(b));
        Ok(e)
    }

    /// The tables hold the fixed code when `fixed` says so.
    pub open spec fn fixed_ok(&self) -> bool {
        fixed_tables(self.fixed, self.lit, self.lit_code, self.dist, self.dist_code)
    }

    /// The decoder's state is consistent with input `b`.
    pub open spec fn inv(&self, b: Seq<u8>) -> bool {
        &&& self.bits_ok(b)
        &&& self.mode <= MODE_DONE
        &&& self.fixed_ok()
        &&& self.mode == MODE_CODES ==> self.table_for(ALPHA_LIT, self.lit_lens@) && self.table_for(
            ALPHA_DIST,
            self.dist_lens@,
        )
        &&& self.mode == MODE_CODES && self.copy_len > 0 ==> 1 <= self.copy_dist <= self.out_pos
            && self.copy_dist <= 32768
        &&& self.mode != MODE_CODES ==> self.copy_len == 0
        &&& self.mode == MODE_STORED ==> self.cnt % 8 == 0
    }

    /// What the spec still has to decode from this state, given the output
    /// `o` so far: the result `inflate_blocks` will reach.
    #[verifier::opaque]
    pub open spec fn rest(&self, b: Seq<u8>, o: Seq<u8>) -> Option<(int, Seq<u8>)> {
        let pos = self.pos();
        if self.mode == MODE_HEADER {
            if self.last {
                Some((pos, o))
            } else {
                inflate_blocks(b, pos, o)
            }
        } else if self.mode == MODE_STORED {
            after(b, self.last, stored_rest(b, pos, self.stored_left as nat, o))
        } else if self.mode == MODE_CODES {
            after(
                b,
                self.last,
                inflate_codes(
                    b,
                    pos,
                    copy_match(o, self.copy_dist as nat, self.copy_len as nat),
                    self.lit_lens@,
                    self.dist_lens@,
                ),
            )
        } else {
            Some((pos, o))
        }
    }

    /// Everything but the bit reader, the scratch tables and `lens` is as
    /// in `o`.
    pub open spec fn same_reader_but_bits(&self, o: &Inflater) -> bool {
        &&& self.out_pos == o.out_pos
        &&& self.mode == o.mode
        &&& self.last == o.last
        &&& self.stored_left == o.stored_left
        &&& self.copy_len == o.copy_len
        &&& self.copy_dist == o.copy_dist
        &&& self.fixed == o.fixed
        &&& self.lit == o.lit
        &&& self.dist == o.dist
        &&& self.lit_code == o.lit_code
        &&& self.dist_code == o.dist_code
        &&& self.lit_lens == o.lit_lens
        &&& self.dist_lens == o.dist_lens
    }

    /// The bit reader and block state are as in `o`.
    pub open spec fn same_reader(&self, o: &Inflater) -> bool {
        &&& self.buf == o.buf
        &&& self.cnt == o.cnt
        &&& self.in_pos == o.in_pos
        &&& self.out_pos == o.out_pos
        &&& self.mode == o.mode
        &&& self.last == o.last
        &&& self.stored_left == o.stored_left
        &&& self.copy_len == o.copy_len
        &&& self.copy_dist == o.copy_dist
    }

    fn build_fixed(&mut self)
        ensures
            final(self).same_reader(old(self)),
            final(self).fixed,
            final(self).fixed_ok(),
            final(self).lit_lens@ == fixed_lit_lens(),
            final(self).dist_lens@ == fixed_dist_lens(),
            final(self).table_for(ALPHA_LIT, fixed_lit_lens()),
            final(self).table_for(ALPHA_DIST, fixed_dist_lens()),
            final(self).work@ <= old(self).work@ + fixed_cost(),
    {
        let mut i: usize = 0;
        while i < 288
            invariant
                i <= 288,
                self.same_reader(old(self)),
                forall|k: int| 0 <= k < i ==> #[trigger] self.lens@[k] == fixed_lit_lens()[k],
                self.work@ == old(self).work@ + i,
            decreases 288 - i,
        {
            self.work = Ghost(self.work@ + 1);
            self.lens[i] = if i < 144 {
                8
            } else if i < 256 {
                9
            } else if i < 280 {
                7
            } else {
                8
            };
            i = i + 1;
        }
        proof {
            lemma_fixed_valid();
            lemma2_to64();
            assert(self.lens@.subrange(0, 288) =~= fixed_lit_lens());
        }
        let (ok1, Ghost(w1)) = build(
            &mut self.lit_code,
            &mut self.lit,
            LIT_BITS,
            vstd::slice::slice_subrange(self.lens.as_slice(), 0, 288),
            ALPHA_LIT,
            true,
        );
        self.work = Ghost(self.work@ + w1);
        let ghost wb = self.work@;
        proof {
            assert(w1 <= 9353) by {
                lemma2_to64();
            }
        }
        let mut i: usize = 0;
        while i < 32
            invariant
                i <= 32,
                self.same_reader(old(self)),
                self.work@ == wb + i,
                ok1,
                table_ok(self.lit@, fixed_lit_lens(), 11, ALPHA_LIT),
                code_ok(self.lit_code, fixed_lit_lens()),
                forall|k: int| 0 <= k < i ==> #[trigger] self.lens@[k] == fixed_dist_lens()[k],
            decreases 32 - i,
        {
            self.work = Ghost(self.work@ + 1);
            self.lens[i] = 5;
            i = i + 1;
        }
        proof {
            assert(self.lens@.subrange(0, 32) =~= fixed_dist_lens());
        }
        let (ok2, Ghost(w2)) = build(
            &mut self.dist_code,
            &mut self.dist,
            DIST_BITS,
            vstd::slice::slice_subrange(self.lens.as_slice(), 0, 32),
            ALPHA_DIST,
            true,
        );
        self.work = Ghost(self.work@ + w2);
        proof {
            assert(w2 <= 1161) by {
                lemma2_to64();
            }
        }
        self.fixed = ok1 && ok2;
        self.lit_lens = Ghost(fixed_lit_lens());
        self.dist_lens = Ghost(fixed_dist_lens());
        proof {
            reveal(fixed_tables);
        }
    }

    /// Reads a dynamic block header and builds its tables.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
    fn read_dynamic(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).bits_ok(b),
            old(self).fixed_ok(),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).bits_ok(b),
            final(self).fixed_ok(),
            final(self).out_pos == old(self).out_pos,
            final(self).mode == old(self).mode,
            final(self).last == old(self).last,
            final(self).stored_left == old(self).stored_left,
            final(self).copy_len == old(self).copy_len,
            final(self).copy_dist == old(self).copy_dist,
            st == Status::Done || st == Status::BadData || st == Status::Truncated,
            st == Status::Done ==> read_dynamic(b, old(self).pos()) == Some(
                (final(self).pos(), final(self).lit_lens@, final(self).dist_lens@),
            ) && final(self).table_for(ALPHA_LIT, final(self).lit_lens@) && final(self).table_for(
                ALPHA_DIST,
                final(self).dist_lens@,
            ),
            st == Status::BadData ==> read_dynamic(b, old(self).pos()) is None,
            st == Status::Truncated ==> final(self).in_pos == input@.len() && (input@ == b ==> read_dynamic(
                b,
                old(self).pos(),
            ) is None),
            st == Status::Truncated ==> (read_dynamic(b, old(self).pos()) matches Some((p2, _, _)) ==> p2 > nbits(
                input@,
            )),
            st == Status::Done ==> final(self).pos() >= old(self).pos() + 26,
            final(self).work@ <= old(self).work@ + dynamic_cost(),
    {
        let ghost p = self.pos();
        proof {
            lemma_bits_bound(b, p, 5);
            lemma_bits_bound(b, p + 5, 5);
            lemma_bits_bound(b, p + 10, 4);
            lemma2_to64();
        }
        proof {
            lemma_read_dynamic_end(b, p);
        }
        let hlit = match self.take(input, Ghost(b), 5) {
            Some(v) => v as usize + 257,
            None => return Status::Truncated,
        };
        let hdist = match self.take(input, Ghost(b), 5) {
            Some(v) => v as usize + 1,
            None => return Status::Truncated,
        };
        let hclen = match self.take(input, Ghost(b), 4) {
            Some(v) => v as usize + 4,
            None => return Status::Truncated,
        };
        if hlit > 286 || hdist > 30 {
            return Status::BadData;
        }
        let ghost q = self.pos();
        proof {
            lemma_clen_order();
        }
        let mut clens = [0u8; 19];
        let mut i: usize = 0;
        while i < hclen
            invariant
                i <= hclen <= 19,
                self.bits_ok(b),
                self.fixed_ok(),
                self.same_reader_but_bits(old(self)),
                prefix(input@, b),
                self.in_pos <= input@.len(),
                p == old(self).pos(),
                q == p + 14,
                self.pos() == q + 3 * i,
                read_dynamic(b, p) matches Some((p2, _, _)) ==> p2 >= q + 3 * hclen,
                hlit == bits(b, p, 5) + 257,
                hdist == bits(b, p + 5, 5) + 1,
                hclen == bits(b, p + 10, 4) + 4,
                hlit <= 286,
                hdist <= 30,
                forall|s: int| 0 <= s < 19 ==> #[trigger] clens@[s] == if clen_slot()[s] < i {
                    bits(b, q + 3 * clen_slot()[s], 3) as u8
                } else {
                    0u8
                },
                self.work@ <= old(self).work@ + 21 + 8 * i,
            decreases hclen - i,
        {
            self.work = Ghost(self.work@ + 1);
            let ghost pi = self.pos();
            let v = match self.take(input, Ghost(b), 3) {
                Some(v) => v,
                None => return Status::Truncated,
            };
            proof {
                lemma_bits_bound(b, pi, 3);
                lemma2_to64();
            }
            let si = CLEN_ORDER[i] as usize;
            let ghost old_clens = clens@;
            clens[si] = v as u8;
            proof {
                assert(clen_slot()[si as int] == i);
                assert forall|s: int| 0 <= s < 19 implies #[trigger] clens@[s] == if clen_slot()[s] < i
                    + 1 {
                    bits(b, q + 3 * clen_slot()[s], 3) as u8
                } else {
                    0u8
                } by {
                    if s != si {
                        assert(clen_order()[clen_slot()[s] as int] == s);
                        assert(clen_slot()[s] != i);
                        assert(clens@[s] == old_clens[s]);
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(clens@ =~= clen_lens(b, q, hclen as nat));
        }
        let (ok, Ghost(wc)) = build(&mut self.cl_code, &mut self.cl, CL_BITS, clens.as_slice(), ALPHA_CL, false);
        self.work = Ghost(self.work@ + wc);
        proof {
            assert(wc <= 671) by {
                lemma2_to64();
            }
        }
        if !ok {
            return Status::BadData;
        }
        let ghost wq2 = self.work@;
        let ghost cl = clens@;
        let total = hlit + hdist;
        let ghost q2 = self.pos();
        let mut n: usize = 0;
        proof {
            assert(self.lens@.subrange(0, 0) =~= Seq::<u8>::empty());
        }
        while n < total
            invariant
                n <= total <= 316,
                self.bits_ok(b),
                self.fixed_ok(),
                self.same_reader_but_bits(old(self)),
                prefix(input@, b),
                self.in_pos <= input@.len(),
                self.table_for(ALPHA_CL, cl),
                p == old(self).pos(),
                q == p + 14,
                q2 == q + 3 * hclen,
                q2 <= nbits(b),
                hlit == bits(b, p, 5) + 257,
                hdist == bits(b, p + 5, 5) + 1,
                hclen == bits(b, p + 10, 4) + 4,
                hlit <= 286,
                hdist <= 30,
                total == hlit + hdist,
                cl == clen_lens(b, q, hclen as nat),
                valid_lens(cl, false),
                self.pos() >= q2,
                read_lens(cl, b, self.pos(), self.lens@.subrange(0, n as int), total as nat)
                    == read_lens(cl, b, q2, Seq::empty(), total as nat),
                wq2 <= old(self).work@ + 844,
                self.work@ <= wq2 + 31 * n,
            decreases total - n,
        {
            self.work = Ghost(self.work@ + 1);
            let ghost pn = self.pos();
            let ghost ln = self.lens@.subrange(0, n as int);
            proof {
                lemma_decode_from_end(cl, b, pn, 1);
            }
            proof {
                lemma_read_lens_step(cl, b, pn, ln, total as nat);
            }
            let e = match self.decode_careful(input, Ghost(b), ALPHA_CL, Ghost(cl)) {
                Ok(e) => e,
                Err(s) => return s,
            };
            let ghost (gs, gl) = decode(cl, b, pn)->Some_0;
            proof {
                lemma_ent(ALPHA_CL, gs, gl);
            }
            let sym = e >> 16;
            if sym < 16 {
                self.lens[n] = sym as u8;
                proof {
                    assert(self.lens@.subrange(0, n + 1) =~= ln.push(sym as u8));
                }
                n = n + 1;
            } else {
                let (eb, base) = if sym == 16 {
                    (2, 3)
                } else if sym == 17 {
                    (3, 3)
                } else {
                    (7, 11)
                };
                if sym == 16 && n == 0 {
                    return Status::BadData;
                }
                let v = if sym == 16 {
                    self.lens[n - 1]
                } else {
                    0
                };
                proof {
                    lemma_bits_bound(b, pn + gl, eb as nat);
                    lemma2_to64();
                }
                let rep = match self.take(input, Ghost(b), eb) {
                    Some(x) => x as usize + base,
                    None => return Status::Truncated,
                };
                if rep > total - n {
                    return Status::BadData;
                }
                let mut k: usize = 0;
                let ghost wk = self.work@;
                while k < rep
                    invariant
                        self.work@ == wk + k,
                        k <= rep,
                        n + rep <= total <= 316,
                        self.lens@.subrange(0, n as int) == ln,
                        forall|j: int| n <= j < n + k ==> #[trigger] self.lens@[j] == v,
                        self.bits_ok(b),
                        self.fixed_ok(),
                        self.same_reader_but_bits(old(self)),
                        self.table_for(ALPHA_CL, cl),
                    decreases rep - k,
                {
                    self.work = Ghost(self.work@ + 1);
                    self.lens[n + k] = v;
                    proof {
                        assert(self.lens@.subrange(0, n as int) =~= ln);
                    }
                    k = k + 1;
                }
                proof {
                    assert(self.lens@.subrange(0, (n + rep) as int) =~= ln + Seq::new(
                        rep as nat,
                        |i: int| v,
                    ));
                    if sym == 16 {
                        assert(ln.last() == v);
                    }
                }
                n = n + rep;
            }
        }
        let ghost lens = self.lens@.subrange(0, total as int);
        proof {
            lemma_read_lens_end(cl, b, q2, Seq::empty(), total as nat);
            assert(lens.subrange(0, hlit as int) =~= self.lens@.subrange(0, hlit as int));
            assert(lens.subrange(hlit as int, total as int) =~= self.lens@.subrange(
                hlit as int,
                total as int,
            ));
        }
        if self.lens[256] == 0 {
            return Status::BadData;
        }
        self.fixed = false;
        proof {
            reveal(fixed_tables);
        }
        proof {
            lemma2_to64();
        }
        let (ok, Ghost(wl)) = build(
            &mut self.lit_code,
            &mut self.lit,
            LIT_BITS,
            vstd::slice::slice_subrange(self.lens.as_slice(), 0, hlit),
            ALPHA_LIT,
            true,
        );
        self.work = Ghost(self.work@ + wl);
        if !ok {
            return Status::BadData;
        }
        let (ok, Ghost(wd)) = build(
            &mut self.dist_code,
            &mut self.dist,
            DIST_BITS,
            vstd::slice::slice_subrange(self.lens.as_slice(), hlit, total),
            ALPHA_DIST,
            true,
        );
        self.work = Ghost(self.work@ + wd);
        if !ok {
            return Status::BadData;
        }
        self.lit_lens = Ghost(lens.subrange(0, hlit as int));
        self.dist_lens = Ghost(lens.subrange(hlit as int, total as int));
        Status::Done
    }

    /// Decodes a block header and sets the mode for its body. If the input
    /// ends inside the header, nothing is consumed (the state is restored),
    /// so decoding can resume when more input arrives.
    fn read_header(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_HEADER,
            !old(self).last,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            st != Status::BadData ==> final(self).inv(b),
            final(self).out_pos == old(self).out_pos,
            st == Status::Done || st == Status::BadData || st == Status::Truncated,
            st == Status::Done ==> final(self).mode != MODE_HEADER && final(self).pos() > old(
                self,
            ).pos() && forall|o: Seq<u8>| #[trigger]
                final(self).rest(b, o) == old(self).rest(b, o),
            st == Status::BadData ==> forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) is None,
            st == Status::Truncated ==> (input@ == b ==> forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) is None),
            st == Status::Truncated ==> forall|o: Seq<u8>| #[trigger] past(old(self).rest(b, o), nbits(input@)),
            st == Status::Truncated ==> final(self).pos() == old(self).pos() && final(self).mode
                == MODE_HEADER && forall|o: Seq<u8>| #[trigger]
                final(self).rest(b, o) == old(self).rest(b, o),
            final(self).work@ <= old(self).work@ + header_cost(),
            st == Status::Done ==> final(self).work@ + credit(final(self).fixed, final(self).mode)
                + 1 <= old(self).work@ + credit(old(self).fixed, old(self).mode) + bit_cost() * (final(
                self).pos() - old(self).pos()),
    {
        let (buf, cnt, in_pos) = (self.buf, self.cnt, self.in_pos);
        let s = self.read_header_inner(input, Ghost(b));
        if s == Status::Truncated {
            self.buf = buf;
            self.cnt = cnt;
            self.in_pos = in_pos;
            proof {
                assert forall|o: Seq<u8>| #[trigger] self.rest(b, o) == old(self).rest(b, o) by {
                    reveal(Inflater::rest);
                }
            }
        }
        s
    }

#[verifier::spinoff_prover]
#[verifier::rlimit(80)]
    fn read_header_inner(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_HEADER,
            !old(self).last,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            st == Status::Done || st == Status::BadData || st == Status::Truncated,
            final(self).out_pos == old(self).out_pos,
            st == Status::Done ==> final(self).inv(b) && final(self).mode != MODE_HEADER
                && final(self).pos() > old(self).pos() && forall|o: Seq<u8>| #[trigger]
                final(self).rest(b, o) == old(self).rest(b, o),
            st == Status::BadData ==> forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) is None,
            st == Status::Truncated ==> final(self).in_pos == input@.len() && (input@ == b ==> forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) is None),
            st == Status::Truncated ==> forall|o: Seq<u8>| #[trigger] past(old(self).rest(b, o), nbits(input@)),
            st == Status::Truncated ==> final(self).fixed_ok() && final(self).mode == MODE_HEADER
                && final(self).copy_len == 0 && final(self).last == old(self).last,
            final(self).work@ <= old(self).work@ + header_cost(),
            st == Status::Done ==> final(self).work@ + credit(final(self).fixed, final(self).mode)
                + 1 <= old(self).work@ + credit(old(self).fixed, old(self).mode) + bit_cost() * (final(
                self).pos() - old(self).pos()),
    {
        let ghost pos = self.pos();
        let h = match self.take(input, Ghost(b), 3) {
            Some(h) => h,
            None => {
                proof {
                    if input@ == b {
                        assert forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) is None by {
                            reveal(Inflater::rest);
                        }
                    }
                    lemma_blocks_hdr_past(b, pos, nbits(input@));
                    assert forall|o: Seq<u8>| #[trigger] past(old(self).rest(b, o), nbits(input@)) by {
                        reveal(Inflater::rest);
                        assert(past(inflate_blocks(b, pos, o), nbits(input@)));
                    }
                }
                return Status::Truncated;
            },
        };
        let ghost p = pos + 3;
        let ghost bfinal = bits(b, pos, 1) == 1;
        proof {
            lemma_bits_split(b, pos, 1, 2);
            lemma_bits_bound(b, pos + 1, 2);
            lemma_bits_bound(b, pos, 1);
            lemma2_to64();
            assert(h & 1 == h % 2) by (bit_vector);
            assert(h >> 1u32 == h / 2) by (bit_vector);
            assert forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) == after(b, bfinal, block(b, pos, o))
                by {
                reveal(Inflater::rest);
                lemma_blocks_unfold(b, pos, o);
            }
            lemma_after_none(b, bfinal);
            assert(bits(b, pos + 1, 2) == h / 2);
            assert(bfinal == (h & 1 == 1));
        }
        let btype = h >> 1;
        if btype == 0 {
            let st = self.stored_header(input, Ghost(b), h);
            proof {
                assert forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) == after(
                    b,
                    bfinal,
                    inflate_stored(b, p, o),
                ) by {
                    lemma_block_cases(b, pos, o);
                }
                if st == Status::Truncated {
                    assert forall|o: Seq<u8>| #[trigger] past(old(self).rest(b, o), nbits(input@)) by {
                        lemma_after_none(b, bfinal);
                        assert(past(inflate_stored(b, p, o), nbits(input@)));
                        if let Some((q, o2)) = inflate_stored(b, p, o) {
                            lemma_after_pos(b, bfinal, q, o2);
                        }
                    }
                }
            }
            st
        } else if btype == 1 {
            self.fixed_header(input, Ghost(b), h);
            proof {
                assert forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) == after(
                    b,
                    bfinal,
                    inflate_codes(b, p, o, fixed_lit_lens(), fixed_dist_lens()),
                ) by {
                    lemma_block_cases(b, pos, o);
                }
            }
            Status::Done
        } else if btype == 2 {
            let st = self.dynamic_header(input, Ghost(b), h);
            proof {
                assert forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) == after(
                    b,
                    bfinal,
                    match read_dynamic(b, p) {
                        None => None,
                        Some((p2, lit, dist)) => inflate_codes(b, p2, o, lit, dist),
                    },
                ) by {
                    lemma_block_cases(b, pos, o);
                }
                if st == Status::Truncated {
                    assert forall|o: Seq<u8>| #[trigger] past(old(self).rest(b, o), nbits(input@)) by {
                        lemma_after_none(b, bfinal);
                        if let Some((p2, lit, dist)) = read_dynamic(b, p) {
                            lemma_codes_end(b, p2, o, lit, dist);
                            if let Some((q, o2)) = inflate_codes(b, p2, o, lit, dist) {
                                lemma_after_pos(b, bfinal, q, o2);
                            }
                        }
                    }
                }
            }
            st
        } else {
            proof {
                assert forall|o: Seq<u8>| #[trigger] old(self).rest(b, o) is None by {
                    lemma_block_cases(b, pos, o);
                }
            }
            Status::BadData
        }
    }

    /// A fixed block's header is just its 3 bits `h`.
    fn fixed_header(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, h: u32)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_HEADER,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            final(self).inv(b),
            final(self).mode == MODE_CODES,
            final(self).pos() == old(self).pos(),
            final(self).out_pos == old(self).out_pos,
            forall|o: Seq<u8>| #[trigger]
                final(self).rest(b, o) == after(
                    b,
                    h & 1 == 1,
                    inflate_codes(b, old(self).pos(), o, fixed_lit_lens(), fixed_dist_lens()),
                ),
            final(self).fixed,
            final(self).work@ + fixed_credit(final(self).fixed) <= old(self).work@ + fixed_credit(
                old(self).fixed,
            ),
            final(self).work@ <= old(self).work@ + fixed_cost(),
    {
        if !self.fixed {
            self.build_fixed();
        }
        proof {
            reveal(fixed_tables);
        }
        self.lit_lens = Ghost(fixed_lit_lens());
        self.dist_lens = Ghost(fixed_dist_lens());
        self.last = h & 1 == 1;
        self.mode = MODE_CODES;
        proof {
            assert forall|o: Seq<u8>| #[trigger] self.rest(b, o) == after(
                b,
                h & 1 == 1,
                inflate_codes(b, old(self).pos(), o, fixed_lit_lens(), fixed_dist_lens()),
            ) by {
                reveal(Inflater::rest);
                assert(copy_match(o, self.copy_dist as nat, 0) == o);
            }
        }
    }

    /// A dynamic block's header after its 3 bits `h`.
    fn dynamic_header(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, h: u32) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_HEADER,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            st == Status::Done || st == Status::BadData || st == Status::Truncated,
            final(self).out_pos == old(self).out_pos,
            st == Status::Done ==> final(self).inv(b) && final(self).mode == MODE_CODES
                && final(self).pos() >= old(self).pos() && read_dynamic(b, old(self).pos())
                == Some((final(self).pos(), final(self).lit_lens@, final(self).dist_lens@))
                && forall|o: Seq<u8>| #[trigger]
                final(self).rest(b, o) == after(
                    b,
                    h & 1 == 1,
                    inflate_codes(
                        b,
                        final(self).pos(),
                        o,
                        final(self).lit_lens@,
                        final(self).dist_lens@,
                    ),
                ),
            st == Status::BadData ==> read_dynamic(b, old(self).pos()) is None,
            st == Status::Truncated ==> final(self).in_pos == input@.len() && (input@ == b ==> read_dynamic(b, old(self).pos()) is None),
            st == Status::Truncated ==> (read_dynamic(b, old(self).pos()) matches Some((p2, _, _)) ==> p2 > nbits(input@)),
            st == Status::Truncated ==> final(self).fixed_ok() && final(self).mode == MODE_HEADER
                && final(self).copy_len == 0 && final(self).last == old(self).last,
            st == Status::Done ==> final(self).pos() >= old(self).pos() + 26,
            final(self).work@ <= old(self).work@ + dynamic_cost(),
    {
        let s = self.read_dynamic(input, Ghost(b));
        if s == Status::Done {
            self.last = h & 1 == 1;
            self.mode = MODE_CODES;
            proof {
                let p = old(self).pos();
                if p + 14 <= nbits(b) {
                    let hclen = bits(b, p + 10, 4) + 4;
                    lemma_read_lens_end(
                        clen_lens(b, p + 14, hclen),
                        b,
                        p + 14 + 3 * hclen,
                        Seq::empty(),
                        bits(b, p, 5) + 257 + bits(b, p + 5, 5) + 1,
                    );
                }
                assert forall|o: Seq<u8>| #[trigger] self.rest(b, o) == after(
                    b,
                    h & 1 == 1,
                    inflate_codes(b, self.pos(), o, self.lit_lens@, self.dist_lens@),
                ) by {
                    reveal(Inflater::rest);
                    assert(copy_match(o, self.copy_dist as nat, 0) == o);
                }
            }
        }
        s
    }

    /// The rest of a stored block's header, after its 3 header bits `h`:
    /// skip to a byte boundary, then LEN and NLEN.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn stored_header(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, h: u32) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_HEADER,
            old(self).pos() >= 3,
            h == bits(b, old(self).pos() - 3, 3),
            h / 2 == 0,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            st == Status::Done || st == Status::BadData || st == Status::Truncated,
            final(self).out_pos == old(self).out_pos,
            st == Status::Done ==> final(self).inv(b) && final(self).mode == MODE_STORED
                && final(self).pos() > old(self).pos() && forall|o: Seq<u8>| #[trigger]
                final(self).rest(b, o) == after(
                    b,
                    h & 1 == 1,
                    inflate_stored(b, old(self).pos(), o),
                ),
            st == Status::BadData ==> forall|o: Seq<u8>| #[trigger] inflate_stored(b, old(self).pos(), o) is None,
            st == Status::Truncated ==> final(self).in_pos == input@.len() && (input@ == b ==> forall|o: Seq<u8>| #[trigger] inflate_stored(b, old(self).pos(), o) is None),
            st == Status::Truncated ==> forall|o: Seq<u8>| #[trigger] past(inflate_stored(b, old(self).pos(), o), nbits(input@)),
            st == Status::Truncated ==> final(self).fixed_ok() && final(self).mode == MODE_HEADER
                && final(self).copy_len == 0 && final(self).last == old(self).last,
            final(self).fixed == old(self).fixed,
            final(self).work@ <= old(self).work@ + 2 * refill_cost(),
    {
        let ghost p = self.pos();
        let r = self.cnt % 8;
        proof {
            lemma_shr_bits(b, self.pos(), self.cnt as nat, self.buf, r as u64);
        }
        self.buf = self.buf >> (r as u64);
        self.cnt = self.cnt - r;
        let ghost i = self.pos() / 8;
        proof {
            assert(self.pos() == 8 * i);
            assert(i == (p + 7) / 8);
        }
        let len = match self.take(input, Ghost(b), 16) {
            Some(v) => v as usize,
            None => return Status::Truncated,
        };
        let nlen = match self.take(input, Ghost(b), 16) {
            Some(v) => v as usize,
            None => return Status::Truncated,
        };
        proof {
            lemma_bits_split(b, 8 * i, 8, 8);
            lemma_bits_split(b, 8 * i + 16, 8, 8);
            lemma_bits_byte(b, i);
            lemma_bits_byte(b, i + 1);
            lemma_bits_byte(b, i + 2);
            lemma_bits_byte(b, i + 3);
            assert(8 * i + 8 == 8 * (i + 1));
            assert(8 * i + 16 == 8 * (i + 2));
            assert(8 * i + 24 == 8 * (i + 3));
            lemma2_to64();
        }
        if len + nlen != 0xffff {
            return Status::BadData;
        }
        self.last = h & 1 == 1;
        self.stored_left = len;
        self.mode = MODE_STORED;
        proof {
            assert(self.pos() == 8 * (i + 4));
            assert((8 * (i + 4)) / 8 == i + 4);
            assert forall|o: Seq<u8>| #[trigger] self.rest(b, o) == after(
                b,
                h & 1 == 1,
                inflate_stored(b, p, o),
            ) by {
                lemma_rest_stored(*self, b, o);
            }
        }
        Status::Done
    }

    /// Copies the whole bytes in the bit buffer of the stored block (it is
    /// byte-aligned here). Returns true if the output filled up first.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
    fn stored_drain(&mut self, Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (full: bool)
        requires
            old(self).inv(b),
            old(self).mode == MODE_STORED,
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos == old(self).in_pos,
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            final(self).inv(b),
            final(self).mode == MODE_STORED,
            final(self).pos() >= old(self).pos(),
            final(self).rest(b, final(out)@.subrange(0, final(self).out_pos as int)) == old(
                self,
            ).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            full ==> final(self).out_pos == final(out)@.len(),
            !full ==> final(self).stored_left == 0 || final(self).cnt == 0,
            final(self).fixed == old(self).fixed,
            final(self).work@ + old(self).pos() <= old(self).work@ + final(self).pos() + 1,
    {
        let ghost o0 = out@.subrange(0, self.out_pos as int);
        while self.stored_left > 0 && self.cnt >= 8
            invariant
                self.inv(b),
                self.mode == MODE_STORED,
                out@.len() == old(out)@.len(),
                old(self).out_pos <= self.out_pos <= out@.len(),
                out@.subrange(0, old(self).out_pos as int) == o0,
                o0 == old(out)@.subrange(0, old(self).out_pos as int),
                self.pos() >= old(self).pos(),
                self.rest(b, out@.subrange(0, self.out_pos as int)) == old(self).rest(b, o0),
                self.fixed == old(self).fixed,
                self.work@ + old(self).pos() <= old(self).work@ + self.pos(),
            decreases self.stored_left,
        {
            let ghost s0 = *self;
            self.work = Ghost(self.work@ + 1);
            proof {
                lemma_rest_same(*self, s0, b, out@.subrange(0, self.out_pos as int));
            }
            if self.out_pos >= out.len() {
                return true;
            }
            let ghost pos = self.pos();
            let ghost o = out@.subrange(0, self.out_pos as int);
            proof {
                lemma_bits_divmod(b, pos, 8, self.cnt as nat);
                lemma_bits_byte(b, pos / 8);
                assert(8 * (pos / 8) == pos);
                lemma2_to64();
                let x = self.buf;
                assert((x as u8) as u64 == x % 256) by (bit_vector);
                lemma_shr_bits(b, pos, self.cnt as nat, self.buf, 8);
                lemma_stored_step(b, pos, self.stored_left as nat, 1, o);
                lemma_rest_stored(*self, b, o);
            }
            set(out, self.out_pos, self.buf as u8);
            proof {
                assert(out@.subrange(0, self.out_pos + 1) =~= o + b.subrange(pos / 8, pos / 8 + 1));
                assert(out@.subrange(0, old(self).out_pos as int) =~= o0);
            }
            self.out_pos = self.out_pos + 1;
            self.buf = self.buf >> 8;
            self.cnt = self.cnt - 8;
            self.stored_left = self.stored_left - 1;
            proof {
                lemma_rest_stored(*self, b, out@.subrange(0, self.out_pos as int));
            }
        }
        false
    }

    /// Copies as much of the stored block as fits and is available: first
    /// the whole bytes already in the bit buffer, then straight from the
    /// input.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
    fn stored(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_STORED,
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            final(self).out_pos <= final(out)@.len(),
            final(self).out_pos >= old(self).out_pos,
            st == Status::Done || st == Status::NeedOutput || st == Status::Truncated,
            final(self).inv(b),
            final(self).pos() >= old(self).pos(),
            final(self).rest(b, final(out)@.subrange(0, final(self).out_pos as int)) == old(
                self,
            ).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            st == Status::Done ==> final(self).mode == MODE_HEADER,
            st != Status::Done ==> final(self).mode == MODE_STORED,
            st == Status::NeedOutput ==> final(self).out_pos == final(out)@.len(),
            st == Status::Truncated ==> final(self).in_pos == input@.len() && (input@ == b ==> old(
                self,
            ).rest(b, old(out)@.subrange(0, old(self).out_pos as int)) is None),
            st == Status::Truncated ==> past(old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)), nbits(input@)),
            final(self).fixed == old(self).fixed,
            final(self).work@ <= old(self).work@ + 2 * (final(self).pos() - old(self).pos()) + 1,
    {
        if self.stored_drain(Ghost(b), out) {
            return Status::NeedOutput;
        }
        let ghost out1 = out@;
        let n = self.stored_left;
        let room = out.len() - self.out_pos;
        let avail = input.len() - self.in_pos;
        let mut k = if n < room {
            n
        } else {
            room
        };
        if avail < k {
            k = avail;
        }
        let ghost pos = self.pos();
        let ghost o = out@.subrange(0, self.out_pos as int);
        proof {
            if n > 0 {
                assert(self.cnt == 0);
            }
            if k > 0 {
                assert(pos == 8 * self.in_pos);
                assert(pos / 8 == self.in_pos);
            }
            lemma_stored_step(b, pos, n as nat, k as nat, o);
            lemma_rest_stored(*self, b, o);
        }
        copy_in(out, self.out_pos, input, self.in_pos, k);
        self.work = Ghost(self.work@ + k as nat);
        proof {
            assert(out@.subrange(0, self.out_pos + k) =~= o + b.subrange(pos / 8, pos / 8 + k));
            assert(out@.subrange(0, old(self).out_pos as int) =~= out1.subrange(
                0,
                old(self).out_pos as int,
            ));
        }
        self.out_pos = self.out_pos + k;
        self.in_pos = self.in_pos + k;
        self.stored_left = n - k;
        proof {
            if k > 0 {
                assert(self.cnt == 0);
                assert(self.buf == 0);
            }
        }
        let ghost o2 = out@.subrange(0, self.out_pos as int);
        proof {
            lemma_rest_stored(*self, b, o2);
            assert(self.pos() % 8 == 0);
            assert(8 * (self.pos() / 8) == self.pos());
        }
        if self.stored_left == 0 {
            self.mode = MODE_HEADER;
            proof {
                lemma_rest_header(*self, b, o2);
                assert(o2 + b.subrange(self.pos() / 8, self.pos() / 8) =~= o2);
            }
            Status::Done
        } else if self.out_pos >= out.len() {
            Status::NeedOutput
        } else {
            proof {
                if input@ == b {
                    lemma_after_none(b, self.last);
                }
                assert(self.in_pos == input@.len());
                assert(self.cnt == 0);
                lemma_stored_rest_past(b, self.last, self.pos(), self.stored_left as nat, o2);
            }
            Status::Truncated
        }
    }

    /// Copies as much of the pending match as fits, one byte at a time.
    /// Returns true if the match is complete.
    fn flush_copy(&mut self, Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (done: bool)
        requires
            old(self).inv(b),
            old(self).mode == MODE_CODES,
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos == old(self).in_pos,
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            final(self).inv(b),
            final(self).mode == MODE_CODES,
            final(self).pos() == old(self).pos(),
            final(self).rest(b, final(out)@.subrange(0, final(self).out_pos as int)) == old(
                self,
            ).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            done == (final(self).copy_len == 0),
            !done ==> final(self).out_pos == final(out)@.len(),
            final(self).fixed == old(self).fixed,
            final(self).work@ == old(self).work@ + (final(self).out_pos - old(self).out_pos),
    {
        let room = out.len() - self.out_pos;
        let n = if self.copy_len < room {
            self.copy_len
        } else {
            room
        };
        let d = self.copy_dist;
        let start = self.out_pos;
        let mut o = start;
        let end = o + n;
        let ghost o0 = out@.subrange(0, start as int);
        proof {
            assert(copy_match(o0, d as nat, 0) == o0);
        }
        // With room for `copy_fast`'s overrun, copy in 8-byte moves: on
        // highly repetitive input most matches end up here, as the input is
        // too short for the fast loop.
        if n > 0 && n <= 258 && out.len() >= 40 && end <= out.len() - 40 {
            let _ = copy_fast(out, start, d, n, Ghost(o0));
            self.work = Ghost((self.work@ + n) as nat);
            o = end;
        }
        while o < end
            invariant
                start <= o <= end <= out@.len(),
                out@.len() == old(out)@.len(),
                start == old(self).out_pos,
                o0 == old(out)@.subrange(0, start as int),
                n > 0 ==> 1 <= d <= start,
                end == start + n,
                out@.subrange(0, o as int) == copy_match(o0, d as nat, (o - start) as nat),
                self.work@ == old(self).work@ + (o - start),
                self.fixed == old(self).fixed,
            decreases end - o,
        {
            self.work = Ghost(self.work@ + 1);
            let ghost k = (o - start) as nat;
            let ghost r = out@.subrange(0, o as int);
            proof {
                lemma_copy_match_push(o0, d as nat, k);
                lemma_copy_match_len(o0, d as nat, k);
            }
            let v = get(out, o - d);
            set(out, o, v);
            proof {
                assert(out@.subrange(0, o + 1) =~= r.push(r[r.len() - d]));
                assert((o + 1 - start) as nat == k + 1);
            }
            o = o + 1;
        }
        let ghost oldlen = self.copy_len;
        self.out_pos = end;
        self.copy_len = self.copy_len - n;
        proof {
            lemma_copy_match_split(o0, d as nat, n as nat, self.copy_len as nat);
            assert(n as nat + self.copy_len as nat == oldlen as nat);
            lemma_rest_codes(*old(self), b, o0);
            lemma_rest_codes(*self, b, out@.subrange(0, end as int));
            if n > 0 {
                lemma_copy_match_index(o0, d as nat, n as nat);
                assert(out@.subrange(0, start as int) =~= out@.subrange(0, end as int).subrange(
                    0,
                    start as int,
                ));
            } else {
                assert(out@.subrange(0, start as int) == o0);
            }
        }
        self.copy_len == 0
    }

    /// Decodes the rest of a compressed block.
    #[inline(always)]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    fn codes(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_CODES,
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            st == Status::Done ==> final(self).mode == MODE_HEADER && final(self).pos() > old(
                self,
            ).pos(),
            st == Status::NeedOutput ==> final(self).mode == MODE_CODES && final(self).pos() >= old(
                self,
            ).pos() && final(self).out_pos == final(out)@.len(),
            st == Status::Done || st == Status::NeedOutput ==> final(self).inv(b) && final(self).rest(b, final(out)@.subrange(0, final(self).out_pos as int)) == old(self).rest(
                b,
                old(out)@.subrange(0, old(self).out_pos as int),
            ),
            st == Status::BadData ==> old(self).rest(
                b,
                old(out)@.subrange(0, old(self).out_pos as int),
            ) is None,
            st == Status::Truncated ==> final(self).inv(b) && final(self).mode == MODE_CODES
                && final(self).pos() >= old(self).pos() && final(self).rest(
                b,
                final(out)@.subrange(0, final(self).out_pos as int),
            ) == old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)) && (input@ == b
                ==> old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)) is None),
            st == Status::Truncated ==> past(old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)), nbits(input@)),
            final(self).fixed == old(self).fixed,
            st == Status::Done || st == Status::NeedOutput || st == Status::Truncated ==> final(self).work@ + 1 <= old(
                self,
            ).work@ + iter_cost() * (final(self).pos() - old(self).pos()) + (final(self).out_pos
                - old(self).out_pos) + body_cost(),
            final(self).work@ + 1 <= old(self).work@ + iter_cost() * (nbits(input@) - old(self).pos())
                + (final(self).out_pos - old(self).out_pos) + body_cost(),
    {
        let ghost o0 = old(out)@.subrange(0, old(self).out_pos as int);
        let ghost goal = old(self).rest(b, o0);
        if self.copy_len > 0 && !self.flush_copy(Ghost(b), out) {
            return Status::NeedOutput;
        }
        let ghost out1 = out@;
        let ghost p1 = self.out_pos;
        let ghost s1 = *self;
        proof {
            assert(out1.subrange(0, old(self).out_pos as int) == o0);
            assert(s1.rest(b, out1.subrange(0, p1 as int)) == goal);
        }
        let r = self.fast(input, Ghost(b), out);
        proof {
            if r == Some(Status::BadData) {
                assert(s1.rest(b, out1.subrange(0, p1 as int)) is None);
                assert(goal is None);
            }
        }
        proof {
            assert forall|i: int| 0 <= i < old(self).out_pos implies out@[i] == o0[i] by {
                assert(out@.subrange(0, p1 as int)[i] == out1.subrange(0, p1 as int)[i]);
                assert(out1.subrange(0, old(self).out_pos as int)[i] == o0[i]);
            }
            assert(out@.subrange(0, old(self).out_pos as int) =~= o0);
        }
        match r {
            Some(s) => return s,
            None => {},
        }
        let ghost w2 = self.work@;
        let ghost pos2 = self.pos();
        let ghost q2 = self.out_pos;
        proof {
            assert(w2 <= old(self).work@ + iter_cost() * (pos2 - old(self).pos()) + (q2 - old(
                self,
            ).out_pos));
        }
        loop
            invariant
                prefix(input@, b),
                self.in_pos <= input@.len(),
                self.fixed == old(self).fixed,
                pos2 >= old(self).pos(),
                q2 >= old(self).out_pos,
                w2 <= old(self).work@ + iter_cost() * (pos2 - old(self).pos()) + (q2 - old(
                    self,
                ).out_pos),
                self.pos() >= pos2,
                self.out_pos >= q2,
                self.work@ <= w2 + 51 * (self.pos() - pos2) + (self.out_pos - q2),
                self.inv(b),
                self.mode == MODE_CODES,
                self.copy_len == 0,
                out@.len() == old(out)@.len(),
                old(self).out_pos <= self.out_pos <= out@.len(),
                out@.subrange(0, old(self).out_pos as int) == o0,
                self.pos() >= old(self).pos(),
                self.rest(b, out@.subrange(0, self.out_pos as int)) == goal,
                goal == old(self).rest(b, o0),
                o0 == old(out)@.subrange(0, old(self).out_pos as int),
            decreases nbits(b) - self.pos(),
        {
            let ghost s0 = *self;
            self.work = Ghost(self.work@ + 1);
            proof {
                lemma_rest_same(*self, s0, b, out@.subrange(0, self.out_pos as int));
                assert(self.pos() <= nbits(b));
            }
            let ghost out1 = out@;
            let ghost p1 = self.out_pos;
            // If the input ends inside this symbol, go back to its start.
            let (buf, cnt, in_pos) = (self.buf, self.cnt, self.in_pos);
            let ghost wh = self.work@;
            let ghost ph = self.pos();
            let ghost qh = self.out_pos;
            let r = self.careful_step(input, Ghost(b), out);
            proof {
                assert(self.work@ <= wh + 50 + (self.out_pos - qh));
                assert(wh <= w2 + 51 * (ph - pos2) + (qh - q2) + 1);
                if r is None {
                    assert(self.pos() >= ph + 1);
                    assert(51 * (ph - pos2) + 51 <= 51 * (self.pos() - pos2));
                }
                assert forall|i: int| 0 <= i < old(self).out_pos implies out@[i] == o0[i] by {
                    assert(out@.subrange(0, p1 as int)[i] == out1.subrange(0, p1 as int)[i]);
                    assert(out1.subrange(0, old(self).out_pos as int)[i] == o0[i]);
                }
                assert(out@.subrange(0, old(self).out_pos as int) =~= o0);
            }
            proof {
                if r == Some(Status::BadData) || (r == Some(Status::Truncated) && input@ == b) {
                    assert(goal is None);
                }
                if r == Some(Status::Truncated) {
                    assert(out1.subrange(0, p1 as int) == out1.subrange(0, p1 as int));
                    assert(past(goal, nbits(input@)));
                }
            }
            match r {
                None => {},
                Some(s) => {
                    if s == Status::Truncated || s == Status::BadData {
                        self.buf = buf;
                        self.cnt = cnt;
                        self.in_pos = in_pos;
                        proof {
                            if s == Status::Truncated {
                                assert(self.pos() == ph);
                                lemma_rest_same(*self, s0, b, out@.subrange(0, self.out_pos as int));
                            }
                        }
                    }
                    return s;
                },
            }
        }
    }

    /// Decodes one symbol with the careful (checked) path.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn careful_step(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (r: Option<Status>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_CODES,
            old(self).copy_len == 0,
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok() == old(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            r is None ==> final(self).mode == MODE_CODES && final(self).copy_len == 0 && final(
                self).pos() > old(self).pos(),
            r == Some(Status::Done) ==> final(self).mode == MODE_HEADER && final(self).pos() > old(
                self).pos(),
            r == Some(Status::NeedOutput) ==> final(self).mode == MODE_CODES && final(self).pos()
                >= old(self).pos() && final(self).out_pos == final(out)@.len(),
            r is None || r == Some(Status::Done) || r == Some(Status::NeedOutput) ==> final(
                self).inv(b) && final(self).rest(
                b,
                final(out)@.subrange(0, final(self).out_pos as int),
            ) == old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            r == Some(Status::BadData) ==> old(self).rest(
                b,
                old(out)@.subrange(0, old(self).out_pos as int),
            ) is None,
            r == Some(Status::Truncated) ==> final(self).same_but_bits(old(self)) && final(out)@ == old(
                out,
            )@ && (input@ == b ==> old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int))
                is None),
            r == Some(Status::Truncated) ==> past(old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)), nbits(input@)),
            final(self).fixed == old(self).fixed,
            final(self).work@ <= old(self).work@ + step_cost() + (final(self).out_pos - old(
                self,
            ).out_pos),
    {
        let ghost pos = self.pos();
        let ghost o = out@.subrange(0, self.out_pos as int);
        let ghost lit = self.lit_lens@;
        let ghost dist = self.dist_lens@;
        proof {
            lemma_rest_codes(*self, b, o);
            assert(copy_match(o, self.copy_dist as nat, 0) == o);
            lemma_decode_from_end(lit, b, pos, 1);
        }
        let e = match self.peek(input, Ghost(b), ALPHA_LIT, Ghost(self.lit_lens@)) {
            Ok(e) => e,
            Err(s) => {
                proof {
                    if s == Status::BadData || input@ == b {
                        lemma_after_none(b, self.last);
                    }
                    if s == Status::Truncated {
                        lemma_after_none(b, old(self).last);
                        lemma_codes_first(b, pos, o, lit, dist);
                        if let Some((q, o2)) = inflate_codes(b, pos, o, lit, dist) {
                            lemma_after_pos(b, old(self).last, q, o2);
                        }
                    }
                }
                return Some(s);
            },
        };
        let ghost (sym, k) = decode(lit, b, pos)->Some_0;
        proof {
            lemma_ent(ALPHA_LIT, sym, k);
            lemma_rest_same(*self, *old(self), b, o);
        }
        if e & F_LIT != 0 {
            self.careful_lit(input, Ghost(b), out, e)
        } else if e & F_EXC != 0 {
            if e & F_EOB != 0 {
                let _ = self.consume(e, Ghost(b));
                self.mode = MODE_HEADER;
                proof {
                    lemma_codes_eob(b, pos, o, lit, dist, k);
                    lemma_rest_header(*self, b, o);
                }
                return Some(Status::Done);
            }
            proof {
                lemma_codes_bad(b, pos, o, lit, dist, sym, k);
                lemma_after_none(b, self.last);
            }
            Some(Status::BadData)
        } else {
            self.careful_match(input, Ghost(b), out, e)
        }
    }

    /// The literal with entry `e`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn careful_lit(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8], e: u32) -> (r: Option<Status>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_CODES,
            old(self).copy_len == 0,
            old(self).out_pos <= old(out)@.len(),
            decode(old(self).lit_lens@, b, old(self).pos()) matches Some((s, k)) && e == ent(
                ALPHA_LIT,
                s,
                k,
            ) && s < 256 && k <= old(self).cnt && 1 <= k <= 15,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok() == old(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            r is None || r == Some(Status::NeedOutput),
            final(self).mode == MODE_CODES && final(self).copy_len == 0,
            r is None ==> final(self).pos() > old(self).pos(),
            r == Some(Status::NeedOutput) ==> final(self).pos() >= old(self).pos() && final(
                self).out_pos == final(out)@.len(),
            final(self).inv(b) && final(self).rest(
                b,
                final(out)@.subrange(0, final(self).out_pos as int),
            ) == old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            final(self).fixed == old(self).fixed,
            final(self).work == old(self).work,
    {
        let ghost pos = self.pos();
        let ghost o = out@.subrange(0, self.out_pos as int);
        let ghost lit = self.lit_lens@;
        let ghost dist = self.dist_lens@;
        let ghost (sym, k) = decode(lit, b, pos)->Some_0;
        proof {
            lemma_ent(ALPHA_LIT, sym, k);
        }
        // A literal that does not fit leaves the state at the symbol
        // boundary.
        if self.out_pos >= out.len() {
            return Some(Status::NeedOutput);
        }
        let v = self.consume(e, Ghost(b));
        set(out, self.out_pos, v as u8);
        proof {
            lemma_rest_codes(*old(self), b, o);
            assert(copy_match(o, self.copy_dist as nat, 0) == o);
            lemma_codes_lit(b, pos, o, lit, dist, sym, k);
            assert(out@.subrange(0, self.out_pos + 1) =~= o.push(sym as u8));
            assert(out@.subrange(0, old(self).out_pos as int) =~= o);
        }
        self.out_pos = self.out_pos + 1;
        proof {
            lemma_rest_codes(*self, b, out@.subrange(0, self.out_pos as int));
            assert(copy_match(o.push(sym as u8), self.copy_dist as nat, 0) == o.push(sym as u8));
        }
        None
    }

    /// The match whose length symbol has entry `e`.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn careful_match(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8], e: u32) -> (r: Option<Status>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_CODES,
            old(self).copy_len == 0,
            old(self).out_pos <= old(out)@.len(),
            decode(old(self).lit_lens@, b, old(self).pos()) matches Some((s, k)) && e == ent(
                ALPHA_LIT,
                s,
                k,
            ) && 257 <= s <= 285 && k + extra_of(ALPHA_LIT, s) <= old(self).cnt && 1 <= k <= 15,
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok() == old(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            r is None ==> final(self).mode == MODE_CODES && final(self).copy_len == 0 && final(
                self).pos() > old(self).pos(),
            r == Some(Status::NeedOutput) ==> final(self).mode == MODE_CODES && final(self).pos()
                >= old(self).pos() && final(self).out_pos == final(out)@.len(),
            r is None || r == Some(Status::NeedOutput) ==> final(self).inv(b) && final(
                self).rest(b, final(out)@.subrange(0, final(self).out_pos as int)) == old(
                self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            r is None || r == Some(Status::NeedOutput) || r == Some(Status::BadData) || r == Some(
                Status::Truncated),
            r == Some(Status::BadData) ==> old(self).rest(
                b,
                old(out)@.subrange(0, old(self).out_pos as int),
            ) is None,
            r == Some(Status::Truncated) ==> final(self).same_but_bits(old(self)) && final(out)@ == old(
                out,
            )@ && (input@ == b ==> old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int))
                is None),
            r == Some(Status::Truncated) ==> past(old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)), nbits(input@)),
            final(self).fixed == old(self).fixed,
            final(self).work@ <= old(self).work@ + peek_cost() + (final(self).out_pos - old(
                self,
            ).out_pos),
    {
        let ghost pos = self.pos();
        let ghost o = out@.subrange(0, self.out_pos as int);
        let ghost lit = self.lit_lens@;
        let ghost dist = self.dist_lens@;
        let ghost (sym, k) = decode(lit, b, pos)->Some_0;
        proof {
            lemma_rest_codes(*self, b, o);
            assert(copy_match(o, self.copy_dist as nat, 0) == o);
            lemma_ent(ALPHA_LIT, sym, k);
            lemma_tables();
        }
        let len = self.consume(e, Ghost(b)) as usize;
        let ghost p2 = self.pos();
        proof {
            assert(len as nat == len_of(b, sym, pos + k));
            lemma_decode_from_end(dist, b, p2, 1);
        }
        let de = match self.peek(input, Ghost(b), ALPHA_DIST, Ghost(self.dist_lens@)) {
            Ok(de) => de,
            Err(s) => {
                proof {
                    if s == Status::BadData || input@ == b {
                        lemma_codes_match_none(b, pos, o, lit, dist, sym, k);
                        lemma_after_none(b, self.last);
                    }
                    if s == Status::Truncated {
                        lemma_after_none(b, old(self).last);
                        lemma_codes_first(b, pos, o, lit, dist);
                        assert(p2 == pos + k + extra_of(ALPHA_LIT, sym));
                        if let Some((q, o2)) = inflate_codes(b, pos, o, lit, dist) {
                            lemma_after_pos(b, old(self).last, q, o2);
                        }
                    }
                }
                return Some(s);
            },
        };
        let ghost (ds, dl) = decode(dist, b, p2)->Some_0;
        proof {
            lemma_ent(ALPHA_DIST, ds, dl);
        }
        if de & F_EXC != 0 {
            proof {
                lemma_codes_match_none(b, pos, o, lit, dist, sym, k);
                lemma_after_none(b, self.last);
            }
            return Some(Status::BadData);
        }
        let d = self.consume(de, Ghost(b)) as usize;
        if d > self.out_pos {
            proof {
                lemma_codes_match_none(b, pos, o, lit, dist, sym, k);
                lemma_after_none(b, self.last);
            }
            return Some(Status::BadData);
        }
        proof {
            lemma_codes_match(b, pos, o, lit, dist, sym, k, ds, dl);
            lemma_dist_max(b, ds, p2 + dl);
        }
        self.copy_len = len;
        self.copy_dist = d;
        proof {
            lemma_rest_codes(*self, b, o);
        }
        if !self.flush_copy(Ghost(b), out) {
            return Some(Status::NeedOutput);
        }
        None
    }

    /// The entry for the symbol at `p`, which `buf` holds `a >= 11` bits of.
    #[inline(always)]
    fn fast_lookup(&self, buf: u64, Ghost(b): Ghost<Seq<u8>>, Ghost(p): Ghost<int>, Ghost(a): Ghost<
        nat,
    >) -> (e: u32)
        requires
            buf as nat == bits(b, p, a),
            11 <= a,
        ensures
            e == self.lit@[bits(b, p, 11) as int],
    {
        proof {
            lemma_shr_bits(b, p, a, buf, 11);
            lemma_bits_bound(b, p, 11);
            lemma2_to64();
        }
        self.lit[(buf & mask(LIT_BITS)) as usize]
    }

    /// Writes the literal with entry `e` and looks up the next symbol.
    #[inline(always)]
    #[verifier::spinoff_prover]
    fn fast_lit(
        &self,
        out: &mut [u8],
        buf: u64,
        cnt: u32,
        op: usize,
        e: u32,
        Ghost(b): Ghost<Seq<u8>>,
        Ghost(ip): Ghost<int>,
        Ghost(a): Ghost<nat>,
        Ghost(goal): Ghost<Option<(int, Seq<u8>)>>,
    ) -> (r: (u64, u32, usize, u32))
        requires
            fast_bits(b, buf, cnt, ip, a),
            cnt >= 26,
            resolved(self.lit_lens@, ALPHA_LIT, b, 8 * ip - cnt, e),
            e & F_LIT != 0,
            op < old(out)@.len() <= usize::MAX,
            after(
                b,
                self.last,
                inflate_codes(
                    b,
                    8 * ip - cnt,
                    old(out)@.subrange(0, op as int),
                    self.lit_lens@,
                    self.dist_lens@,
                ),
            ) == goal,
        ensures
            final(out)@.len() == old(out)@.len(),
            forall|i: int| 0 <= i < op ==> final(out)@[i] == old(out)@[i],
            r.2 == op + 1,
            cnt - 15 <= r.1 < cnt,
            fast_bits(b, r.0, r.1, ip, (a - (cnt - r.1)) as nat),
            r.3 == self.lit@[bits(b, 8 * ip - r.1, 11) as int],
            after(
                b,
                self.last,
                inflate_codes(
                    b,
                    8 * ip - r.1,
                    final(out)@.subrange(0, op + 1),
                    self.lit_lens@,
                    self.dist_lens@,
                ),
            ) == goal,
    {
        let ghost pos = 8 * ip - cnt;
        let ghost o = out@.subrange(0, op as int);
        let ghost (s, k) = decode(self.lit_lens@, b, pos)->Some_0;
        proof {
            lemma_ent(ALPHA_LIT, s, k);
        }
        let (nb, nc, _v) = fast_take(buf, cnt, e, Ghost(b), Ghost(ip), Ghost(a));
        set(out, op, (e >> 16) as u8);
        proof {
            lemma_codes_lit(b, pos, o, self.lit_lens@, self.dist_lens@, s, k);
            assert(out@.subrange(0, op + 1) =~= o.push(s as u8));
        }
        let ne = self.fast_lookup(nb, Ghost(b), Ghost(8 * ip - nc), Ghost((a - (cnt - nc)) as nat));
        (nb, nc, op + 1, ne)
    }

    /// Decodes the match whose length symbol has entry `e`, refills, looks
    /// up the next symbol and copies the match. `None` if the data is bad.
    #[inline(always)]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn fast_match(
        &self,
        input: &[u8], Ghost(b): Ghost<Seq<u8>>,
        out: &mut [u8],
        buf: u64,
        cnt: u32,
        ip: usize,
        op: usize,
        e: u32,
        Ghost(a): Ghost<nat>,
        Ghost(goal): Ghost<Option<(int, Seq<u8>)>>,
    ) -> (res: (Option<(u64, u32, usize, usize, u32)>, Ghost<nat>))
        requires
            prefix(input@, b),
            self.table_for(ALPHA_LIT, self.lit_lens@),
            self.table_for(ALPHA_DIST, self.dist_lens@),
            fast_bits(b, buf, cnt, ip as int, a),
            cnt >= 56,
            ip + 8 <= input@.len() <= usize::MAX,
            resolved(self.lit_lens@, ALPHA_LIT, b, 8 * ip - cnt, e),
            e & F_LIT == 0,
            e & F_EXC == 0,
            op + FAST_OUT_MARGIN <= old(out)@.len() <= usize::MAX,
            after(
                b,
                self.last,
                inflate_codes(
                    b,
                    8 * ip - cnt,
                    old(out)@.subrange(0, op as int),
                    self.lit_lens@,
                    self.dist_lens@,
                ),
            ) == goal,
        ensures
            final(out)@.len() == old(out)@.len(),
            forall|i: int| 0 <= i < op ==> final(out)@[i] == old(out)@[i],
            res.1@ <= 55,
            match res.0 {
                None => goal is None,
                Some((nb, nc, ni, no, ne)) => {
                    &&& op < no <= op + 258
                    &&& ip <= ni <= ip + 7
                    &&& 8 * ni - nc > 8 * ip - cnt
                    &&& fast_bits(b, nb, nc, ni as int, 64)
                    &&& nc >= 56
                    &&& ne == self.lit@[bits(b, 8 * ni - nc, 11) as int]
                    &&& after(
                        b,
                        self.last,
                        inflate_codes(
                            b,
                            8 * ni - nc,
                            final(out)@.subrange(0, no as int),
                            self.lit_lens@,
                            self.dist_lens@,
                        ),
                    ) == goal
                },
            },
    {
        let ghost pos = 8 * ip - cnt;
        let ghost o = out@.subrange(0, op as int);
        let ghost lit = self.lit_lens@;
        let ghost dist = self.dist_lens@;
        let ghost (s, k) = decode(lit, b, pos)->Some_0;
        proof {
            lemma_ent(ALPHA_LIT, s, k);
            lemma_tables();
        }
        let (buf, cnt2, len) = fast_take(buf, cnt, e, Ghost(b), Ghost(ip as int), Ghost(a));
        let ghost a2 = (a - (e & 0xff)) as nat;
        let ghost p2 = pos + k + len_extra()[s - 257];
        proof {
            assert(len as nat == len_of(b, s, pos + k));
            lemma_len_bound(b, s, pos + k);
            assert(8 * ip - cnt2 == p2);
            lemma_shr_bits(b, p2, a2, buf, 8);
            lemma_bits_bound(b, p2, 8);
            lemma2_to64();
        }
        let len = len as usize;
        let mut de = self.dist[(buf & mask(DIST_BITS)) as usize];
        proof {
            lemma_fast_entry(self.dist@, dist, ALPHA_DIST, 8, b, p2, a2, buf as nat, cnt2 as nat, de);
            lemma_long();
        }
        let ghost mut w: nat = 0;
        if de & F_EXC != 0 {
            if de & F_LONG != 0 {
                let (slow, Ghost(sw)) = decode_slow(&self.dist_code, ALPHA_DIST, buf, cnt2, Ghost(self.dist_lens@));
                proof {
                    w = sw;
                }
                match slow {
                    Some(x) => de = x,
                    None => {
                        proof {
                            lemma_codes_match_none(b, pos, o, lit, dist, s, k);
                            lemma_after_none(b, self.last);
                        }
                        return (None, Ghost(w));
                    },
                }
            }
            if de & F_EXC != 0 {
                proof {
                    let (ds, dl) = decode(dist, b, p2)->Some_0;
                    lemma_ent(ALPHA_DIST, ds, dl);
                    lemma_codes_match_none(b, pos, o, lit, dist, s, k);
                    lemma_after_none(b, self.last);
                }
                return (None, Ghost(w));
            }
        }
        let ghost (ds, dl) = decode(dist, b, p2)->Some_0;
        proof {
            lemma_ent(ALPHA_DIST, ds, dl);
        }
        let (buf, cnt3, d) = fast_take(buf, cnt2, de, Ghost(b), Ghost(ip as int), Ghost(a2));
        let ghost a3 = (a2 - (de & 0xff)) as nat;
        let d = d as usize;
        proof {
            assert(d as nat == dist_base()[ds as int] + bits(b, p2 + dl, dist_extra()[ds as int]));
        }
        if d > op {
            proof {
                lemma_codes_match_none(b, pos, o, lit, dist, s, k);
                lemma_after_none(b, self.last);
            }
            return (None, Ghost(w));
        }
        proof {
            lemma_codes_match(b, pos, o, lit, dist, s, k, ds, dl);
        }
        let (buf, cnt4, ip2) = fast_refill(input, Ghost(b), buf, cnt3, ip, Ghost(a3));
        let ne = self.fast_lookup(buf, Ghost(b), Ghost(8 * ip2 - cnt4), Ghost(64));
        let cw = copy_fast(out, op, d, len, Ghost(o));
        proof {
            lemma_copy_match_index(o, d as nat, len as nat);
            let m = copy_match(o, d as nat, len as nat);
            assert forall|i: int| 0 <= i < op implies out@[i] == old(out)@[i] by {
                assert(out@.subrange(0, op + len)[i] == out@[i]);
                assert(m.subrange(0, op as int)[i] == m[i]);
                assert(o[i] == old(out)@.subrange(0, op as int)[i]);
            }
        }
        (Some((buf, cnt4, ip2, op + len, ne)), Ghost(w + cw@))
    }

    /// Stores the fast loop's bit reader, dropping the bits above `cnt`.
    #[inline(always)]
    fn fast_store(&mut self, buf: u64, cnt: u32, ip: usize, Ghost(b): Ghost<Seq<u8>>, Ghost(a): Ghost<
        nat,
    >)
        requires
            fast_bits(b, buf, cnt, ip as int, a),
        ensures
            final(self).bits_ok(b),
            final(self).same_but_bits(old(self)),
            final(self).pos() == 8 * ip - cnt,
            final(self).in_pos == ip,
            final(self).work == old(self).work,
    {
        proof {
            lemma_shr_bits(b, 8 * ip - cnt, a, buf, cnt as u64);
        }
        self.buf = buf & mask(cnt);
        self.cnt = cnt;
        self.in_pos = ip;
    }

    /// One iteration of the fast loop: up to three literals, or an
    /// end-of-block, or a match.
    #[inline(always)]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    fn fast_iter(
        &self,
        input: &[u8], Ghost(b): Ghost<Seq<u8>>,
        out: &mut [u8],
        buf: u64,
        cnt: u32,
        ip: usize,
        op: usize,
        e: u32,
        Ghost(a): Ghost<nat>,
        Ghost(goal): Ghost<Option<(int, Seq<u8>)>>,
    ) -> (res: (Fast, Ghost<nat>))
        requires
            prefix(input@, b),
            self.table_for(ALPHA_LIT, self.lit_lens@),
            self.table_for(ALPHA_DIST, self.dist_lens@),
            fast_bits(b, buf, cnt, ip as int, a),
            a >= 11,
            e == self.lit@[bits(b, 8 * ip - cnt, 11) as int],
            ip + 16 <= input@.len() <= usize::MAX,
            op + FAST_OUT_MARGIN <= old(out)@.len() <= usize::MAX,
            after(
                b,
                self.last,
                inflate_codes(
                    b,
                    8 * ip - cnt,
                    old(out)@.subrange(0, op as int),
                    self.lit_lens@,
                    self.dist_lens@,
                ),
            ) == goal,
        ensures
            final(out)@.len() == old(out)@.len(),
            forall|i: int| 0 <= i < op ==> final(out)@[i] == old(out)@[i],
            res.1@ <= iter_cost() - 2,
            match res.0 {
                Fast::Next(nb, nc, ni, no, ne, na) => {
                    &&& fast_bits(b, nb, nc, ni as int, na@)
                    &&& ni <= input@.len()
                    &&& na@ >= 11
                    &&& ne == self.lit@[bits(b, 8 * ni - nc, 11) as int]
                    &&& 8 * ni - nc > 8 * ip - cnt
                    &&& op < no <= op + 258
                    &&& after(
                        b,
                        self.last,
                        inflate_codes(
                            b,
                            8 * ni - nc,
                            final(out)@.subrange(0, no as int),
                            self.lit_lens@,
                            self.dist_lens@,
                        ),
                    ) == goal
                },
                Fast::Eob(nb, nc, ni) => {
                    &&& fast_bits(b, nb, nc, ni as int, nc as nat)
                    &&& ni <= input@.len()
                    &&& 8 * ni - nc > 8 * ip - cnt
                    &&& goal == after(
                        b,
                        self.last,
                        Some((8 * ni - nc, final(out)@.subrange(0, op as int))),
                    )
                },
                Fast::Bad => goal is None,
            },
    {
        let ghost mut w: nat = 0;
        let ghost lit = self.lit_lens@;
        let ghost dist = self.dist_lens@;
        // Refill to 56..63 bits: enough for a length, a distance and
        // their extra bits (48), or three literals (45).
        let (buf, cnt, ip) = fast_refill(input, Ghost(b), buf, cnt, ip, Ghost(a));
        let ghost pos = 8 * ip - cnt;
        proof {
            lemma_fast_entry(self.lit@, lit, ALPHA_LIT, 11, b, pos, 64, buf as nat, cnt as nat, e);
            lemma_long();
        }
        if e & F_LIT != 0 {
            let (buf, cnt, op, e) = self.fast_lit(out, buf, cnt, op, e, Ghost(b), Ghost(ip as int), Ghost(64), Ghost(goal));
            let ghost a1 = (64 - (8 * ip - cnt - pos)) as nat;
            proof {
                lemma_fast_entry(self.lit@, lit, ALPHA_LIT, 11, b, 8 * ip - cnt, a1, buf as nat, cnt as nat, e);
            }
            if e & F_LIT == 0 {
                return (Fast::Next(buf, cnt, ip, op, e, Ghost(a1)), Ghost(w));
            }
            let ghost out1 = out@;
            let (buf, cnt, op, e) = self.fast_lit(out, buf, cnt, op, e, Ghost(b), Ghost(ip as int), Ghost(a1), Ghost(goal));
            let ghost a2 = (64 - (8 * ip - cnt - pos)) as nat;
            proof {
                lemma_fast_entry(self.lit@, lit, ALPHA_LIT, 11, b, 8 * ip - cnt, a2, buf as nat, cnt as nat, e);
            }
            if e & F_LIT == 0 {
                return (Fast::Next(buf, cnt, ip, op, e, Ghost(a2)), Ghost(w));
            }
            let (buf, cnt, op, e) = self.fast_lit(out, buf, cnt, op, e, Ghost(b), Ghost(ip as int), Ghost(a2), Ghost(goal));
            let ghost a3 = (64 - (8 * ip - cnt - pos)) as nat;
            return (Fast::Next(buf, cnt, ip, op, e, Ghost(a3)), Ghost(w));
        }
        let mut e = e;
        if e & F_EXC != 0 {
            if e & F_LONG != 0 {
                let (slow, Ghost(sw)) = decode_slow(&self.lit_code, ALPHA_LIT, buf, cnt, Ghost(self.lit_lens@));
                proof {
                    w = sw;
                }
                match slow {
                    Some(x) => e = x,
                    None => {
                        proof {
                            lemma_after_none(b, self.last);
                        }
                        return (Fast::Bad, Ghost(w));
                    },
                }
                if e & F_LIT != 0 {
                    let (buf, cnt, op, e) = self.fast_lit(out, buf, cnt, op, e, Ghost(b), Ghost(ip as int), Ghost(64), Ghost(goal));
                    let ghost a1 = (64 - (8 * ip - cnt - pos)) as nat;
                    return (Fast::Next(buf, cnt, ip, op, e, Ghost(a1)), Ghost(w));
                }
            }
            let ghost (s, k) = decode(lit, b, pos)->Some_0;
            proof {
                lemma_ent(ALPHA_LIT, s, k);
            }
            if e & F_EOB != 0 {
                let (buf, cnt, _v) = fast_take(buf, cnt, e, Ghost(b), Ghost(ip as int), Ghost(64));
                proof {
                    lemma_codes_eob(b, pos, out@.subrange(0, op as int), lit, dist, k);
                    lemma_shr_bits(b, 8 * ip - cnt, (64 - k) as nat, buf, cnt as u64);
                    lemma_bits_bound(b, 8 * ip - cnt, cnt as nat);
                }
                return (Fast::Eob(buf & mask(cnt), cnt, ip), Ghost(w));
            }
            if e & F_EXC != 0 {
                proof {
                    lemma_codes_bad(b, pos, out@.subrange(0, op as int), lit, dist, s, k);
                    lemma_after_none(b, self.last);
                }
                return (Fast::Bad, Ghost(w));
            }
        }
        // A match: length code and extra bits, distance code and extra
        // bits, then the copy.
        let (m, Ghost(mw)) = self.fast_match(input, Ghost(b), out, buf, cnt, ip, op, e, Ghost(64), Ghost(goal));
        match m {
            None => (Fast::Bad, Ghost(w + mw)),
            Some((buf, cnt, ip, op, e)) => (Fast::Next(buf, cnt, ip, op, e, Ghost(64)), Ghost(w + mw)),
        }
    }

    /// The fast loop. Returns `None` when too little input or output is
    /// left for it, with the state at a symbol boundary.
    #[inline(always)]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(40)]
    fn fast(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (r: Option<Status>)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).mode == MODE_CODES,
            old(self).copy_len == 0,
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok() == old(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            r is None || r == Some(Status::Done) || r == Some(Status::BadData),
            r is None ==> final(self).mode == MODE_CODES && final(self).copy_len == 0,
            r == Some(Status::Done) ==> final(self).mode == MODE_HEADER && final(self).pos() > old(
                self,
            ).pos(),
            r is None || r == Some(Status::Done) ==> final(self).inv(b) && final(self).pos()
                >= old(self).pos() && final(self).rest(
                b,
                final(out)@.subrange(0, final(self).out_pos as int),
            ) == old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            r == Some(Status::BadData) ==> old(self).rest(
                b,
                old(out)@.subrange(0, old(self).out_pos as int),
            ) is None,
            final(self).fixed == old(self).fixed,
            r is None || r == Some(Status::Done) ==> final(self).work@ <= old(self).work@ + iter_cost()
                * (final(self).pos() - old(self).pos()),
            r == Some(Status::BadData) ==> final(self).work@ <= old(self).work@ + iter_cost() * (
            nbits(input@) - old(self).pos()) + iter_cost(),
    {
        let ghost lit = self.lit_lens@;
        let ghost dist = self.dist_lens@;
        let ghost p0 = self.out_pos as int;
        let ghost pos0 = self.pos();
        let ghost o0 = old(out)@.subrange(0, p0);
        let ghost goal = old(self).rest(b, o0);
        let mut buf = self.buf;
        let mut cnt = self.cnt;
        let mut ip = self.in_pos;
        let mut op = self.out_pos;
        let in_end = input.len();
        let out_len = out.len();
        // Each iteration refills at most twice, 7 bytes each.
        if in_end < 16 || out_len < FAST_OUT_MARGIN {
            return None;
        }
        let in_fast_end = in_end - 15;
        let out_fast_end = out_len - FAST_OUT_MARGIN;
        if ip >= in_fast_end || op > out_fast_end {
            return None;
        }
        proof {
            lemma_rest_codes(*self, b, o0);
            assert(copy_match(o0, self.copy_dist as nat, 0) == o0);
        }
        let (nb, nc, ni) = fast_refill(input, Ghost(b), buf, cnt, ip, Ghost(cnt as nat));
        buf = nb;
        cnt = nc;
        ip = ni;
        let ghost mut a: nat = 64;
        let ghost mut w: nat = 0;
        // Invariant: `e` is the table entry for the next symbol's low bits.
        let mut e = self.fast_lookup(buf, Ghost(b), Ghost(8 * ip - cnt), Ghost(a));
        while ip < in_fast_end && op <= out_fast_end
            invariant
                prefix(input@, b),
                self.in_pos <= input@.len(),
                in_end == input@.len(),
                ip <= in_end,
                out_len == out@.len(),
                out@.len() == old(out)@.len(),
                in_fast_end == in_end - 15,
                out_fast_end == out_len - FAST_OUT_MARGIN,
                *self == *old(self),
                self.inv(b),
                self.mode == MODE_CODES,
                self.copy_len == 0,
                self.table_for(ALPHA_LIT, lit),
                self.table_for(ALPHA_DIST, dist),
                goal == old(self).rest(b, o0),
                o0 == old(out)@.subrange(0, p0),
                lit == self.lit_lens@,
                dist == self.dist_lens@,
                fast_bits(b, buf, cnt, ip as int, a),
                a >= 11,
                e == self.lit@[bits(b, 8 * ip - cnt, 11) as int],
                p0 <= op <= out_len,
                p0 == old(self).out_pos,
                pos0 == old(self).pos(),
                8 * ip - cnt >= pos0,
                forall|i: int| 0 <= i < p0 ==> out@[i] == old(out)@[i],
                after(b, self.last, inflate_codes(b, 8 * ip - cnt, out@.subrange(0, op as int), lit, dist))
                    == goal,
                w <= iter_cost() * ((8 * ip - cnt) - pos0),
            decreases 8 * in_end - (8 * ip - cnt),
        {
            let ghost out1 = out@;
            let ghost ph = 8 * ip - cnt;
            let (st, Ghost(iw)) = self.fast_iter(input, Ghost(b), out, buf, cnt, ip, op, e, Ghost(a), Ghost(goal));
            proof {
                w = w + 1 + iw;
                assert(ph <= nbits(b));
            }
            proof {
                assert forall|i: int| 0 <= i < p0 implies out@[i] == old(out)@[i] by {
                    assert(out@[i] == out1[i]);
                }
            }
            match st {
                Fast::Next(nb, nc, ni, no, ne, na) => {
                    buf = nb;
                    cnt = nc;
                    ip = ni;
                    op = no;
                    e = ne;
                    proof {
                        a = na@;
                    }
                },
                Fast::Eob(nb, nc, ni) => {
                    self.work = Ghost(self.work@ + w);
                    let ghost s1 = *self;
                    self.fast_store(nb, nc, ni, Ghost(b), Ghost(nc as nat));
                    self.out_pos = op;
                    self.mode = MODE_HEADER;
                    proof {
                        assert(self.fixed_ok() == s1.fixed_ok());
                        lemma_rest_header(*self, b, out@.subrange(0, op as int));
                        assert(out@.subrange(0, p0) =~= o0);
                    }
                    return Some(Status::Done);
                },
                Fast::Bad => {
                    self.work = Ghost(self.work@ + w);
                    return Some(Status::BadData);
                },
            }
        }
        let ghost o = out@.subrange(0, op as int);
        self.work = Ghost(self.work@ + w);
        self.fast_store(buf, cnt, ip, Ghost(b), Ghost(a));
        self.out_pos = op;
        proof {
            lemma_rest_codes(*self, b, o);
            assert(copy_match(o, self.copy_dist as nat, 0) == o);
            assert(out@.subrange(0, p0) =~= o0);
        }
        None
    }

    /// Decodes until the final block ends, the output buffer is full, or
    /// the input turns out bad or short. `out[..self.out_pos]` is the
    /// output so far; call again with a longer `out` (same prefix) after
    /// `NeedOutput`.
    ///
    /// The result is the spec's: `Done` exactly when the stream ends, with
    /// the spec's output and end position; `BadData` or `Truncated` only
    /// when the spec fails (a `Truncated` stream may still be completed by
    /// more input).
    #[inline(always)]
    pub fn run(&mut self, input: &[u8], Ghost(b): Ghost<Seq<u8>>, out: &mut [u8]) -> (st: Status)
        requires
            prefix(input@, b),
            old(self).in_pos <= input@.len(),
            old(self).inv(b),
            old(self).out_pos <= old(out)@.len(),
        ensures
            final(self).in_pos <= input@.len(),
            final(self).fixed_ok(),
            final(out)@.len() == old(out)@.len(),
            final(out)@.subrange(0, old(self).out_pos as int) == old(out)@.subrange(
                0,
                old(self).out_pos as int,
            ),
            old(self).out_pos <= final(self).out_pos <= final(out)@.len(),
            st == Status::Done ==> final(self).inv(b) && final(self).mode == MODE_DONE && old(
                self,
            ).rest(b, old(out)@.subrange(0, old(self).out_pos as int)) == Some(
                (final(self).pos(), final(out)@.subrange(0, final(self).out_pos as int)),
            ),
            st == Status::NeedOutput ==> final(self).inv(b) && final(self).out_pos == final(out)@.len() && final(self).rest(b, final(out)@.subrange(0, final(self).out_pos as int))
                == old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)),
            st == Status::BadData ==> old(self).rest(
                b,
                old(out)@.subrange(0, old(self).out_pos as int),
            ) is None,
            st == Status::Truncated ==> final(self).inv(b) && final(self).rest(
                b,
                final(out)@.subrange(0, final(self).out_pos as int),
            ) == old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)) && (input@ == b
                ==> old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)) is None),
            st == Status::Truncated ==> past(old(self).rest(b, old(out)@.subrange(0, old(self).out_pos as int)), nbits(input@)),
            st == Status::Truncated ==> final(self).pos() >= old(self).pos() && final(self).work@ + credit(
                final(self).fixed,
                final(self).mode,
            ) <= old(self).work@ + credit(old(self).fixed, old(self).mode) + bit_cost() * (final(self).pos() - old(
                self,
            ).pos()) + (final(self).out_pos - old(self).out_pos) + fail_cost(),
            st == Status::Done || st == Status::NeedOutput ==> final(self).pos() >= old(self).pos()
                && final(self).work@ + credit(final(self).fixed, final(self).mode) <= old(self).work@
                + credit(old(self).fixed, old(self).mode) + bit_cost() * (final(self).pos() - old(
                self,
            ).pos()) + (final(self).out_pos - old(self).out_pos) + body_cost(),
            final(self).work@ <= old(self).work@ + credit(old(self).fixed, old(self).mode)
                + bit_cost() * (nbits(input@) - old(self).pos()) + (final(self).out_pos - old(
                self,
            ).out_pos) + header_cost() + body_cost(),
    {
        let ghost o0 = old(out)@.subrange(0, old(self).out_pos as int);
        let ghost goal = old(self).rest(b, o0);
        loop
            invariant
                prefix(input@, b),
                self.in_pos <= input@.len(),
                self.pos() >= old(self).pos(),
                self.work@ + credit(self.fixed, self.mode) <= old(self).work@ + credit(
                    old(self).fixed,
                    old(self).mode,
                ) + 1200 * (self.pos() - old(self).pos()) + (self.out_pos - old(self).out_pos),
                self.inv(b),
                out@.len() == old(out)@.len(),
                old(self).out_pos <= self.out_pos <= out@.len(),
                out@.subrange(0, old(self).out_pos as int) == o0,
                self.rest(b, out@.subrange(0, self.out_pos as int)) == goal,
                goal == old(self).rest(b, o0),
                o0 == old(out)@.subrange(0, old(self).out_pos as int),
            decreases 2 * (nbits(b) - self.pos()) + if self.mode == MODE_STORED || self.mode
                == MODE_CODES {
                1int
            } else {
                0int
            },
        {
            let ghost o = out@.subrange(0, self.out_pos as int);
            let ghost sw = *self;
            self.work = Ghost(self.work@ + 1);
            proof {
                lemma_rest_same(*self, sw, b, o);
                assert(self.pos() <= nbits(b));
            }
            let ghost s0 = *self;
            let ghost wh = self.work@;
            let s = if self.mode == MODE_HEADER {
                if self.last {
                    self.mode = MODE_DONE;
                    proof {
                        lemma_rest_done(s0, b, o);
                        lemma_rest_done(*self, b, o);
                    }
                    return Status::Done;
                }
                self.read_header(input, Ghost(b))
            } else if self.mode == MODE_STORED {
                self.stored(input, Ghost(b), out)
            } else if self.mode == MODE_CODES {
                self.codes(input, Ghost(b), out)
            } else {
                proof {
                    lemma_rest_done(*self, b, o);
                }
                return Status::Done;
            };
            proof {
                if s == Status::Done {
                    if s0.mode == MODE_HEADER {
                        assert(self.work@ + credit(self.fixed, self.mode) + 1 <= wh + credit(
                            s0.fixed,
                            s0.mode,
                        ) + 1200 * (self.pos() - s0.pos()));
                    } else if s0.mode == MODE_STORED {
                        assert(self.work@ <= wh + 2 * (self.pos() - s0.pos()) + 1);
                        assert(credit(s0.fixed, s0.mode) == credit(self.fixed, self.mode) + 130);
                    } else {
                        assert(self.work@ + 1 <= wh + 72 * (self.pos() - s0.pos()) + (self.out_pos
                            - s0.out_pos) + 130);
                        assert(credit(s0.fixed, s0.mode) == credit(self.fixed, self.mode) + 130);
                    }
                }
                if s == Status::BadData || (s == Status::Truncated && input@ == b) {
                    if s0.mode == MODE_HEADER {
                        assert(s0.rest(b, o) is None);
                    }
                }
                if s == Status::Truncated {
                    if s0.mode == MODE_HEADER {
                        assert(past(s0.rest(b, o), nbits(input@)));
                    }
                    assert(past(goal, nbits(input@)));
                    if s0.mode == MODE_HEADER {
                        assert(self.work@ <= wh + header_cost());
                        assert(self.mode == MODE_HEADER);
                        assert(credit(self.fixed, self.mode) <= credit(s0.fixed, s0.mode) + fixed_cost());
                    } else if s0.mode == MODE_STORED {
                        assert(self.work@ <= wh + 2 * (self.pos() - s0.pos()) + 1);
                        assert(credit(s0.fixed, s0.mode) == credit(self.fixed, self.mode));
                    } else {
                        assert(self.work@ + 1 <= wh + 72 * (self.pos() - s0.pos()) + (self.out_pos
                            - s0.out_pos) + 130);
                        assert(credit(s0.fixed, s0.mode) == credit(self.fixed, self.mode));
                    }
                }
                assert(out@.subrange(0, old(self).out_pos as int) =~= o0);
            }
            if s != Status::Done {
                return s;
            }
        }
    }
}

} // verus!
