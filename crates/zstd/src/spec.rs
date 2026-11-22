//! Executable-independent specification of Zstandard decompression
//! (RFC 8878).
//!
//! Everything here is a total function over `Seq<u8>`, written to be read
//! side by side with RFC 8878 (and `doc/zstd_compression_format.md` in the
//! zstd repository). This file, vcore's specs, Verus and the Rust compiler
//! are the trusted base: the exec functions in the crate are proven to
//! compute exactly these functions.
//!
//! Most loops are written in tail form, `run(state) = if done { result }
//! else { run(step(state)) }`, so that each exec loop can be checked one
//! step at a time against them.
//!
//! Where the RFC leaves a choice, the spec follows the reference decoder
//! (libzstd 1.5.x), so that vzstd accepts what libzstd accepts. The
//! exceptions are listed in DEPARTURES.md; each one makes vzstd stricter,
//! where libzstd's one-shot and streaming decoders disagree with each other
//! or read past the data they were given.
#[cfg(verus_only)]
pub use verilith_core::bits::{bit, bits, nbits};
#[cfg(verus_only)]
pub use verilith_core::bytes::{le16, le32};
#[cfg(verus_only)]
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

/// Index of the highest set bit of `x` (0 for 0 and 1).
pub open spec fn highbit(x: nat) -> nat
    decreases x,
{
    if x <= 1 {
        0
    } else {
        1 + highbit(x / 2)
    }
}

/// Little-endian value of the `n` bytes at `i`.
pub open spec fn le(b: Seq<u8>, i: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        b[i] as nat + 256 * le(b, i + 1, (n - 1) as nat)
    }
}

pub open spec fn min(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

// ---------------------------------------------------------------------------
// Backward bitstreams (RFC 8878 §4.1 "FSE bitstreams", §4.2.2)
// ---------------------------------------------------------------------------
//
// Entropy-coded streams are read from their last byte towards their first.
// The bits of the stream are numbered as in `verilith_core::bits` (bit 0 is the
// least significant bit of byte 0), and the last byte's highest set bit is
// an end marker, so the useful bits are 0 .. `bstart(s)`. A reader holds a
// position `p`: the bits below `p` are still unread. Reading `n` bits takes
// the field just below `p`, as a little-endian number.

/// Number of useful bits in a backward stream, or `None` if it is empty or
/// its last byte is zero (no end marker).
pub open spec fn bstart(s: Seq<u8>) -> Option<int> {
    if s.len() == 0 || s[s.len() - 1] == 0 {
        None
    } else {
        Some(8 * (s.len() - 1) + highbit(s[s.len() - 1] as nat))
    }
}

/// The `n` bits just below position `p`, as a number. Where the field
/// reaches below bit 0, the missing low bits read as zeros (this is only
/// used to look up a table before the length of the code is known).
pub open spec fn bpeek(s: Seq<u8>, p: int, n: nat) -> nat {
    if p >= n {
        bits(s, p - n, n)
    } else if p <= 0 {
        0
    } else {
        bits(s, 0, p as nat) * pow2((n - p) as nat)
    }
}

// ---------------------------------------------------------------------------
// FSE table descriptions (§4.1.1)
// ---------------------------------------------------------------------------
//
// A distribution is read forwards, least significant bit first, from bit 4
// of its first byte. Reading past the end of the data it was given is an
// error. (libzstd reads zeros there and checks the length used at the end;
// the outcome is the same, since the position only grows.)

/// The zero-probability repeat flags after a zero probability: 2-bit
/// counts of further zeros, continued while the flag is 3. Returns the new
/// bit position and the number of zeros, `z` plus those read here.
pub open spec fn nc_zeros(b: Seq<u8>, q: int, z: nat) -> Option<(int, nat)>
    decreases 8 * b.len() - q,
{
    if q < 0 || q + 2 > 8 * b.len() {
        None
    } else {
        let f = bits(b, q, 2);
        if f == 3 {
            nc_zeros(b, q + 2, z + 3)
        } else {
            Some((q + 2, z + f))
        }
    }
}

/// One probability field, read with `highbit(rem) + 1` or one bit fewer
/// bits. Returns the decoded value (probability + 1) and the new position.
pub open spec fn nc_value(b: Seq<u8>, q: int, rem: int) -> Option<(int, int)> {
    let t = pow2(highbit(rem as nat)) as int;
    let nb = highbit(rem as nat) + 1;
    let max = 2 * t - 1 - rem;
    if q < 0 || q + nb - 1 > 8 * b.len() {
        None
    } else {
        let low = bits(b, q, (nb - 1) as nat) as int;
        if low < max {
            Some((low, q + nb - 1))
        } else if q + nb > 8 * b.len() {
            None
        } else {
            let v = bits(b, q, nb) as int;
            Some((if v >= t { v - max } else { v }, q + nb))
        }
    }
}

/// Reads probabilities until the remaining points `rem - 1` reach zero.
/// `norm` holds the probabilities so far (-1 for "less than 1"); `prev0`
/// says the last one was zero, so repeat flags come next. At most `maxsv1`
/// symbols. Returns the distribution and the bit position after it.
pub open spec fn nc_run(b: Seq<u8>, q: int, norm: Seq<int>, rem: int, prev0: bool, maxsv1: nat) -> Option<
    (Seq<int>, int),
>
    decreases maxsv1 - norm.len(), if prev0 {
        1int
    } else {
        0int
    },
{
    if norm.len() > maxsv1 || rem < 2 {
        None
    } else if prev0 {
        match nc_zeros(b, q, 0) {
            None => None,
            Some((q2, z)) => {
                let norm2 = norm + Seq::new(z, |i: int| 0int);
                if norm2.len() >= maxsv1 {
                    None
                } else {
                    nc_run(b, q2, norm2, rem, false, maxsv1)
                }
            },
        }
    } else if norm.len() >= maxsv1 {
        None
    } else {
        match nc_value(b, q, rem) {
            None => None,
            Some((v, q2)) => {
                let count = v - 1;
                let rem2 = if count >= 0 {
                    rem - count
                } else {
                    rem - 1
                };
                let norm2 = norm.push(count);
                if rem2 <= 1 {
                    if rem2 == 1 {
                        Some((norm2, q2))
                    } else {
                        None
                    }
                } else if norm2.len() >= maxsv1 {
                    None
                } else {
                    nc_run(b, q2, norm2, rem2, count == 0, maxsv1)
                }
            },
        }
    }
}

/// An FSE table description at the start of `b`, for symbols up to
/// `maxsv` and accuracy logs up to `maxlog`. Returns the accuracy log, the
/// distribution and the number of bytes used.
pub open spec fn fse_desc(b: Seq<u8>, maxsv: nat, maxlog: nat) -> Option<(nat, Seq<int>, int)> {
    if b.len() == 0 {
        None
    } else {
        let log = bits(b, 0, 4) + 5;
        if log > maxlog {
            None
        } else {
            match nc_run(b, 4, Seq::empty(), pow2(log) + 1int, false, maxsv + 1) {
                None => None,
                Some((norm, q)) => Some((log, norm, (q + 7) / 8)),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// FSE decoding tables (§4.1.1 "From normalized distribution to decoding
// tables")
// ---------------------------------------------------------------------------

/// A decoding table row: the symbol, and how to reach the next state
/// (`base` plus the next `nb` bits).
pub struct FseEntry {
    pub sym: nat,
    pub nb: nat,
    pub base: nat,
}

/// A decoding table: its accuracy log and its `2^log` rows.
pub struct FseTable {
    pub log: nat,
    pub rows: Seq<FseEntry>,
}

/// The step between the positions the spread visits.
pub open spec fn fse_step(size: nat) -> nat {
    size / 2 + size / 8 + 3
}

/// Number of "less than 1" probabilities among the first `s` symbols.
pub open spec fn lowprob_count(norm: Seq<int>, s: int) -> nat
    decreases s,
{
    if s <= 0 {
        0
    } else {
        lowprob_count(norm, s - 1) + if norm[s - 1] == -1 {
            1nat
        } else {
            0nat
        }
    }
}

/// Symbols with a "less than 1" probability take the last rows, one each,
/// from the end backwards, in symbol order.
pub open spec fn place_lowprob(norm: Seq<int>, size: nat, s: int, tab: Seq<nat>) -> Seq<nat>
    decreases norm.len() - s,
{
    if s < 0 || s >= norm.len() {
        tab
    } else if norm[s] == -1 {
        place_lowprob(norm, size, s + 1, tab.update(size - 1 - lowprob_count(norm, s), s as nat))
    } else {
        place_lowprob(norm, size, s + 1, tab)
    }
}

/// The next position after `pos` in the spread order, skipping the rows of
/// "less than 1" symbols (those above `high`). `fuel` bounds the search;
/// the step is odd, so the search finds a free row within `size` steps.
pub open spec fn next_pos(pos: nat, size: nat, high: int, fuel: nat) -> nat
    decreases fuel,
{
    let p = (pos + fse_step(size)) % size;
    if p > high && fuel > 0 {
        next_pos(p, size, high, (fuel - 1) as nat)
    } else {
        p
    }
}

/// Lays the other symbols down in symbol order, `norm[s]` rows each, at
/// the positions `0, next_pos(0), next_pos(next_pos(0)), ...`. `i` counts
/// the rows symbol `s` has so far.
pub open spec fn spread(norm: Seq<int>, size: nat, high: int, s: int, i: int, pos: nat, tab: Seq<nat>) -> Seq<
    nat,
>
    decreases norm.len() - s, (if 0 <= s < norm.len() {
        norm[s]
    } else {
        0
    }) - i,
{
    if s < 0 || s >= norm.len() {
        tab
    } else if i >= norm[s] {
        spread(norm, size, high, s + 1, 0, pos, tab)
    } else {
        spread(norm, size, high, s, i + 1, next_pos(pos, size, high, size), tab.update(pos as int, s as nat))
    }
}

/// The symbol in each row.
pub open spec fn fse_symbols(norm: Seq<int>, log: nat) -> Seq<nat> {
    let size = pow2(log);
    let high = size - 1 - lowprob_count(norm, norm.len() as int);
    let tab0 = place_lowprob(norm, size, 0, Seq::new(size, |i: int| 0nat));
    spread(norm, size, high, 0, 0, 0, tab0)
}

/// Number of rows before `u` holding symbol `s`.
pub open spec fn occ(tab: Seq<nat>, s: nat, u: int) -> nat
    decreases u,
{
    if u <= 0 {
        0
    } else {
        occ(tab, s, u - 1) + if tab[u - 1] == s {
            1nat
        } else {
            0nat
        }
    }
}

/// Row `u`: a symbol with `c` rows (1 for "less than 1") numbers them
/// `c, c + 1, ..., 2c - 1` in row order; row number `x` reads
/// `log - highbit(x)` bits and starts its next states at
/// `x * 2^nb - size`. (A symbol with probability 0 has no rows, since the
/// probabilities fill the table exactly; `c` is taken as 1 there only so
/// that the formula is total.)
pub open spec fn fse_row(norm: Seq<int>, log: nat, tab: Seq<nat>, u: int) -> FseEntry {
    let s = tab[u];
    let c = if 0 <= s < norm.len() && norm[s as int] >= 1 {
        norm[s as int] as nat
    } else {
        1nat
    };
    let x = c + occ(tab, s, u);
    let hb = if highbit(x) <= log {
        highbit(x)
    } else {
        log
    };
    let nb = (log - hb) as nat;
    FseEntry { sym: s, nb: nb, base: (x * pow2(nb) - pow2(log)) as nat }
}

pub open spec fn fse_table(norm: Seq<int>, log: nat) -> FseTable {
    let tab = fse_symbols(norm, log);
    FseTable { log: log, rows: Seq::new(pow2(log), |u: int| fse_row(norm, log, tab, u)) }
}

/// The table of RLE mode: one state, symbol `sym`, no bits.
pub open spec fn rle_table(sym: nat) -> FseTable {
    FseTable { log: 0, rows: seq![FseEntry { sym: sym, nb: 0, base: 0 }] }
}

// ---------------------------------------------------------------------------
// Huffman tree descriptions (§4.2.1)
// ---------------------------------------------------------------------------

/// Weights compressed with FSE (§4.2.1.2): two interleaved states share
/// one table and take turns; each emits its symbol, then reads bits for its
/// next state. When a state update runs past the start of the stream, the
/// other state's symbol is the last weight. At most 255 weights.
pub open spec fn fw_run(s: Seq<u8>, t: FseTable, p: int, s1: nat, s2: nat, out: Seq<u8>) -> Option<Seq<u8>>
    decreases 256 - out.len(),
{
    if out.len() > 253 || s1 >= t.rows.len() || s2 >= t.rows.len() {
        None
    } else {
        let e1 = t.rows[s1 as int];
        let out1 = out.push(e1.sym as u8);
        if e1.nb > p {
            Some(out1.push(t.rows[s2 as int].sym as u8))
        } else {
            let n1 = e1.base + bits(s, p - e1.nb, e1.nb);
            let p1 = p - e1.nb;
            if out1.len() > 253 || n1 >= t.rows.len() {
                None
            } else {
                let e2 = t.rows[s2 as int];
                let out2 = out1.push(e2.sym as u8);
                if e2.nb > p1 {
                    Some(out2.push(t.rows[n1 as int].sym as u8))
                } else {
                    let n2 = e2.base + bits(s, p1 - e2.nb, e2.nb);
                    fw_run(s, t, p1 - e2.nb, n1, n2, out2)
                }
            }
        }
    }
}

/// `b` is the `hb` bytes after the header byte: an FSE table description
/// (accuracy log at most 6), then the backward stream of weights.
pub open spec fn fse_weights(b: Seq<u8>) -> Option<Seq<u8>> {
    match fse_desc(b, 255, 6) {
        None => None,
        Some((log, norm, used)) => {
            let s = b.subrange(used, b.len() as int);
            let t = fse_table(norm, log);
            match bstart(s) {
                None => None,
                Some(p) => if p < 2 * log {
                    None
                } else {
                    let s1 = bits(s, p - log, log);
                    let s2 = bits(s, p - 2 * log, log);
                    fw_run(s, t, p - 2 * log, s1, s2, Seq::empty())
                },
            }
        },
    }
}

/// The weights listed in a tree description at the start of `b` (all but
/// the last), and the bytes it uses.
pub open spec fn huf_listed(b: Seq<u8>) -> Option<(Seq<u8>, int)> {
    if b.len() == 0 {
        None
    } else {
        let hb = b[0] as int;
        if hb >= 128 {
            // Direct representation: 4 bits per weight, high nibble first.
            let n = hb - 127;
            let nbytes = (n + 1) / 2;
            if 1 + nbytes > b.len() {
                None
            } else {
                Some(
                    (
                        Seq::new(
                            n as nat,
                            |i: int|
                                if i % 2 == 0 {
                                    b[1 + i / 2] / 16
                                } else {
                                    b[1 + i / 2] % 16
                                },
                        ),
                        1 + nbytes,
                    ),
                )
            }
        } else if 1 + hb > b.len() {
            None
        } else {
            match fse_weights(b.subrange(1, 1 + hb)) {
                None => None,
                Some(w) => Some((w, 1 + hb)),
            }
        }
    }
}

/// Sum of `2^(w-1)` over the nonzero weights.
pub open spec fn wsum(w: Seq<u8>, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        wsum(w, n - 1) + if w[n - 1] == 0 {
            0
        } else {
            pow2((w[n - 1] - 1) as nat)
        }
    }
}

/// Number of weights equal to `x`.
pub open spec fn wcount(w: Seq<u8>, x: u8, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        wcount(w, x, n - 1) + if w[n - 1] == x {
            1nat
        } else {
            0nat
        }
    }
}

/// A Huffman code, as its weights (one per symbol, 0 for absent) and its
/// maximum code length `log`.
pub struct HufCode {
    pub w: Seq<u8>,
    pub log: nat,
}

/// The full code from the listed weights (§4.2.1.1): every weight at most
/// 12 (libzstd's limit; the RFC says 11), the last weight completes the sum
/// to a power of two, and there is an even number, at least 2, of weight-1
/// symbols.
pub open spec fn huf_code(listed: Seq<u8>) -> Option<HufCode> {
    let total = wsum(listed, listed.len() as int);
    if exists|i: int| 0 <= i < listed.len() && listed[i] > 12 {
        None
    } else if total == 0 {
        None
    } else {
        let log = highbit(total) + 1;
        let rest = (pow2(log) - total) as nat;
        if log > 12 || pow2(highbit(rest)) != rest {
            None
        } else {
            let w = listed.push((highbit(rest) + 1) as u8);
            let ones = wcount(w, 1, w.len() as int);
            if ones < 2 || ones % 2 == 1 {
                None
            } else {
                Some(HufCode { w: w, log: log })
            }
        }
    }
}

/// The decoding table (§4.2.1.3): symbols sorted by weight, then by value;
/// a symbol of weight `x` takes `2^(x-1)` consecutive rows, each giving the
/// symbol and its code length `log + 1 - x`. Row `v` decodes the code whose
/// `log` bits, most significant first, are `v`.
pub open spec fn huf_rows_from(c: HufCode, x: nat, s: int) -> Seq<(u8, u8)>
    decreases c.log + 1 - x, c.w.len() - s,
{
    if x > c.log || x == 0 {
        Seq::empty()
    } else if s >= c.w.len() || s < 0 {
        huf_rows_from(c, x + 1, 0)
    } else if c.w[s] as nat == x {
        Seq::new(pow2((x - 1) as nat), |i: int| (s as u8, (c.log + 1 - x) as u8)) + huf_rows_from(
            c,
            x,
            s + 1,
        )
    } else {
        huf_rows_from(c, x, s + 1)
    }
}

pub open spec fn huf_rows(c: HufCode) -> Seq<(u8, u8)> {
    huf_rows_from(c, 1, 0)
}

/// A tree description at the start of `b`: the code and the bytes used.
pub open spec fn huf_desc(b: Seq<u8>) -> Option<(HufCode, int)> {
    match huf_listed(b) {
        None => None,
        Some((listed, used)) => match huf_code(listed) {
            None => None,
            Some(c) => Some((c, used)),
        },
    }
}

// ---------------------------------------------------------------------------
// Huffman-coded streams (§4.2.2)
// ---------------------------------------------------------------------------

/// Decodes `n` more symbols from position `p`: look at the next `log`
/// bits, take the row's symbol and consume its code length.
pub open spec fn huf_run(rows: Seq<(u8, u8)>, log: nat, s: Seq<u8>, p: int, n: nat, out: Seq<u8>) -> Option<
    (Seq<u8>, int),
>
    decreases n,
{
    if n == 0 {
        Some((out, p))
    } else {
        let v = bpeek(s, p, log);
        if v >= rows.len() {
            None
        } else {
            let (sym, len) = rows[v as int];
            if len as int > p {
                None
            } else {
                huf_run(rows, log, s, p - len, (n - 1) as nat, out.push(sym))
            }
        }
    }
}

/// A whole stream decoding to exactly `n` symbols, using all its bits.
pub open spec fn huf_stream(c: HufCode, s: Seq<u8>, n: nat) -> Option<Seq<u8>> {
    match bstart(s) {
        None => None,
        Some(p) => match huf_run(huf_rows(c), c.log, s, p, n, Seq::empty()) {
            None => None,
            Some((out, p2)) => if p2 == 0 {
                Some(out)
            } else {
                None
            },
        },
    }
}

/// Four streams after a 6-byte jump table: the first three each decode
/// `(n + 3) / 4` symbols, the fourth the rest.
pub open spec fn huf_4streams(c: HufCode, b: Seq<u8>, n: nat) -> Option<Seq<u8>> {
    if b.len() < 10 {
        None
    } else {
        let l1 = le(b, 0, 2) as int;
        let l2 = le(b, 2, 2) as int;
        let l3 = le(b, 4, 2) as int;
        let l4 = b.len() - 6 - l1 - l2 - l3;
        let seg = (n + 3) / 4;
        if l4 < 0 || 3 * seg > n {
            None
        } else {
            let a1: int = 6;
            let a2 = a1 + l1;
            let a3 = a2 + l2;
            let a4 = a3 + l3;
            match (
                huf_stream(c, b.subrange(a1, a2), seg),
                huf_stream(c, b.subrange(a2, a3), seg),
                huf_stream(c, b.subrange(a3, a4), seg),
                huf_stream(c, b.subrange(a4, b.len() as int), (n - 3 * seg) as nat),
            ) {
                (Some(o1), Some(o2), Some(o3), Some(o4)) => Some(o1 + o2 + o3 + o4),
                _ => None,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Literals section (§3.1.1.3.1)
// ---------------------------------------------------------------------------

/// Decoded literals, the bytes the section used, and the Huffman code to
/// keep for later treeless sections.
pub struct Lits {
    pub lits: Seq<u8>,
    pub used: int,
    pub huf: Option<HufCode>,
}

/// The literals section at the start of block content `b`. `bmax` is the
/// frame's maximum block size; `huf` is the code from the last section
/// that had one. Header size rules follow libzstd: a block shorter than 2
/// bytes, or a Huffman-coded section in a block shorter than 5, is an
/// error even when the header itself is shorter.
#[verifier::opaque]
pub open spec fn lit_section(b: Seq<u8>, bmax: nat, huf: Option<HufCode>) -> Option<Lits> {
    if b.len() < 2 {
        None
    } else {
        let ty = b[0] % 4;
        let sf = (b[0] / 4) % 4;
        if ty == 0 || ty == 1 {
            // Raw or RLE: size format 0 or 2 is a 5-bit size in a 1-byte
            // header; 1 a 12-bit size in 2 bytes; 3 a 20-bit size in 3.
            let lh: int = if sf == 1 {
                2
            } else if sf == 3 {
                3
            } else {
                1
            };
            let n: int = if sf == 1 {
                le(b, 0, 2) as int / 16
            } else if sf == 3 {
                if b.len() < 3 {
                    0
                } else {
                    le(b, 0, 3) as int / 16
                }
            } else {
                b[0] as int / 8
            };
            if b.len() < lh || n > bmax {
                None
            } else if ty == 0 {
                if lh + n > b.len() {
                    None
                } else {
                    Some(Lits { lits: b.subrange(lh, lh + n), used: lh + n, huf: huf })
                }
            } else if lh + 1 > b.len() {
                None
            } else {
                Some(Lits { lits: Seq::new(n as nat, |i: int| b[lh]), used: lh + 1, huf: huf })
            }
        } else if b.len() < 5 {
            None
        } else if ty == 3 && huf is None {
            None
        } else {
            // Compressed (2) or treeless (3). Size format 0: one stream,
            // 10-bit sizes in a 3-byte header; 1: four streams, same sizes;
            // 2: 14-bit sizes in 4 bytes; 3: 18-bit sizes in 5 bytes.
            let lhc = le(b, 0, 4) as int;
            let lh: int = if sf <= 1 {
                3
            } else if sf == 2 {
                4
            } else {
                5
            };
            let n: int = if sf <= 1 {
                (lhc / 16) % 1024
            } else if sf == 2 {
                (lhc / 16) % 16384
            } else {
                (lhc / 16) % 262144
            };
            let c: int = if sf <= 1 {
                (lhc / 16384) % 1024
            } else if sf == 2 {
                lhc / 262144
            } else {
                lhc / 4194304 + b[4] as int * 1024
            };
            if n > bmax || (sf != 0 && n < 6) || lh + c > b.len() {
                None
            } else {
                let region = b.subrange(lh, lh + c);
                let code: Option<(HufCode, int)> = if ty == 2 {
                    huf_desc(region)
                } else {
                    Some((huf.unwrap(), 0))
                };
                match code {
                    None => None,
                    Some((hc, tu)) => {
                        let streams = region.subrange(tu, region.len() as int);
                        let out = if sf == 0 {
                            huf_stream(hc, streams, n as nat)
                        } else {
                            huf_4streams(hc, streams, n as nat)
                        };
                        match out {
                            None => None,
                            Some(lits) => Some(Lits { lits: lits, used: lh + c, huf: Some(hc) }),
                        }
                    },
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Sequences section (§3.1.1.3.2)
// ---------------------------------------------------------------------------

/// Literals length codes: baseline and extra bits.
pub open spec fn ll_base(c: nat) -> nat {
    if c < 16 {
        c
    } else {
        seq![16nat, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536][c - 16]
    }
}

pub open spec fn ll_bits(c: nat) -> nat {
    if c < 16 {
        0
    } else {
        seq![1nat, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16][c - 16]
    }
}

/// Match length codes: baseline and extra bits.
pub open spec fn ml_base(c: nat) -> nat {
    if c < 32 {
        c + 3
    } else {
        seq![35nat, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051, 4099, 8195, 16387, 32771, 65539][c - 32]
    }
}

pub open spec fn ml_bits(c: nat) -> nat {
    if c < 32 {
        0
    } else {
        seq![1nat, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16][c - 32]
    }
}

/// The predefined distributions (§3.1.1.3.2.2).
pub open spec fn ll_default() -> Seq<int> {
    seq![
        4int, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1,
        -1, -1, -1, -1,
    ]
}

pub open spec fn ml_default() -> Seq<int> {
    seq![
        1int, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1,
    ]
}

pub open spec fn of_default() -> Seq<int> {
    seq![
        1int, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1,
    ]
}

/// Largest symbol and accuracy log of each table kind: literals lengths
/// (0), offsets (1), match lengths (2).
pub open spec fn kind_maxsv(k: nat) -> nat {
    if k == 0 {
        35
    } else if k == 1 {
        31
    } else {
        52
    }
}

pub open spec fn kind_maxlog(k: nat) -> nat {
    if k == 1 {
        8
    } else {
        9
    }
}

pub open spec fn kind_default(k: nat) -> FseTable {
    if k == 0 {
        fse_table(ll_default(), 6)
    } else if k == 1 {
        fse_table(of_default(), 5)
    } else {
        fse_table(ml_default(), 6)
    }
}

/// One table of the sequences header, in mode `mode`, at the start of `b`.
/// `prev` is the table of the same kind from the last block with
/// sequences, if any. Returns the table and the bytes used.
pub open spec fn seq_table(b: Seq<u8>, k: nat, mode: nat, prev: Option<FseTable>) -> Option<(FseTable, int)> {
    if mode == 0 {
        Some((kind_default(k), 0))
    } else if mode == 1 {
        if b.len() < 1 || b[0] as nat > kind_maxsv(k) {
            None
        } else {
            Some((rle_table(b[0] as nat), 1))
        }
    } else if mode == 2 {
        match fse_desc(b, kind_maxsv(k), kind_maxlog(k)) {
            None => None,
            Some((log, norm, used)) => Some((fse_table(norm, log), used)),
        }
    } else {
        match prev {
            None => None,
            Some(t) => Some((t, 0)),
        }
    }
}

/// The repeat offsets, most recent first.
pub struct Reps {
    pub r1: nat,
    pub r2: nat,
    pub r3: nat,
}

/// The three tables of the last block with sequences.
pub struct SeqTables {
    pub ll: FseTable,
    pub of: FseTable,
    pub ml: FseTable,
}

/// One decoded sequence.
pub struct Seqn {
    pub ll: nat,
    pub ml: nat,
    pub off: nat,
}

/// The offset of a sequence (§3.1.1.5): offset code `oc` with value
/// `ov = 2^oc + extra bits`; values 1 to 3 are repeat offsets, shifted by
/// one when the literals length is zero. Returns the offset and the new
/// repeat offsets; an offset of 0 (repeat offset 1 minus one) is an error.
pub open spec fn resolve_offset(ov: nat, ll0: bool, r: Reps) -> Option<(nat, Reps)> {
    if ov > 3 {
        let off = (ov - 3) as nat;
        Some((off, Reps { r1: off, r2: r.r1, r3: r.r2 }))
    } else {
        let idx = if ll0 {
            ov + 1
        } else {
            ov
        };
        if idx == 1 {
            Some((r.r1, r))
        } else if idx == 2 {
            Some((r.r2, Reps { r1: r.r2, r2: r.r1, r3: r.r3 }))
        } else if idx == 3 {
            Some((r.r3, Reps { r1: r.r3, r2: r.r1, r3: r.r2 }))
        } else if r.r1 <= 1 {
            None
        } else {
            let off = (r.r1 - 1) as nat;
            Some((off, Reps { r1: off, r2: r.r1, r3: r.r2 }))
        }
    }
}

/// The state of a block's sequence decoder: the backward stream position,
/// the three FSE states, the repeat offsets, the literals used so far and
/// the output of the frame so far.
pub struct SeqState {
    pub p: int,
    pub sll: nat,
    pub sof: nat,
    pub sml: nat,
    pub reps: Reps,
    pub li: int,
    pub out: Seq<u8>,
}

/// `out` followed by `len` bytes copied from `dist` back, one at a time,
/// so the copy may overlap its own output.
pub open spec fn copy_match(out: Seq<u8>, dist: nat, len: nat) -> Seq<u8>
    decreases len,
{
    if len == 0 {
        out
    } else {
        copy_match(out.push(out[out.len() - dist]), dist, (len - 1) as nat)
    }
}

/// Decodes and executes `n` more sequences (§3.1.1.3.2.1.1 and §3.1.1.4):
/// read the offset's extra bits, then the match length's, then the literals
/// length's; copy that many literals, then the match. Unless it is the
/// last sequence, update the literals length state, then the match length
/// state, then the offset state. An offset may reach back to the start of
/// the frame and at most `window` bytes.
#[verifier::opaque]
pub open spec fn seq_run(t: SeqTables, s: Seq<u8>, lits: Seq<u8>, window: nat, n: nat, st: SeqState) -> Option<
    SeqState,
>
    decreases n,
{
    if n == 0 {
        Some(st)
    } else if st.sll >= t.ll.rows.len() || st.sof >= t.of.rows.len() || st.sml >= t.ml.rows.len() {
        None
    } else {
        let ell = t.ll.rows[st.sll as int];
        let eof = t.of.rows[st.sof as int];
        let eml = t.ml.rows[st.sml as int];
        let oc = eof.sym;
        let mlb = ml_bits(eml.sym);
        let llb = ll_bits(ell.sym);
        let p0 = st.p;
        if oc + mlb + llb > p0 {
            None
        } else {
            let ov = pow2(oc) + bits(s, p0 - oc, oc);
            let p1 = p0 - oc;
            let ml = ml_base(eml.sym) + bits(s, p1 - mlb, mlb);
            let p2 = p1 - mlb;
            let ll = ll_base(ell.sym) + bits(s, p2 - llb, llb);
            let p3 = p2 - llb;
            match resolve_offset(ov, ll == 0, st.reps) {
                None => None,
                Some((off, reps)) => {
                    if st.li + ll > lits.len() {
                        None
                    } else {
                        let out1 = st.out + lits.subrange(st.li, st.li + ll);
                        if off > out1.len() || off > window || off == 0 {
                            None
                        } else {
                            let out2 = copy_match(out1, off, ml);
                            let li = st.li + ll;
                            if n == 1 {
                                Some(SeqState { p: p3, sll: st.sll, sof: st.sof, sml: st.sml, reps: reps, li: li, out: out2 })
                            } else if ell.nb + eml.nb + eof.nb > p3 {
                                None
                            } else {
                                let sll = ell.base + bits(s, p3 - ell.nb, ell.nb);
                                let p4 = p3 - ell.nb;
                                let sml = eml.base + bits(s, p4 - eml.nb, eml.nb);
                                let p5 = p4 - eml.nb;
                                let sof = eof.base + bits(s, p5 - eof.nb, eof.nb);
                                let p6 = p5 - eof.nb;
                                seq_run(
                                    t,
                                    s,
                                    lits,
                                    window,
                                    (n - 1) as nat,
                                    SeqState { p: p6, sll: sll, sof: sof, sml: sml, reps: reps, li: li, out: out2 },
                                )
                            }
                        }
                    }
                },
            }
        }
    }
}

/// The number of sequences at the start of `b` and the bytes it uses.
pub open spec fn nb_seq(b: Seq<u8>) -> Option<(nat, int)> {
    if b.len() < 1 {
        None
    } else if b[0] < 128 {
        Some((b[0] as nat, 1))
    } else if b[0] < 255 {
        if b.len() < 2 {
            None
        } else {
            Some((((b[0] - 128) * 256 + b[1]) as nat, 2))
        }
    } else if b.len() < 3 {
        None
    } else {
        Some(((b[1] + 256 * b[2] + 0x7f00) as nat, 3))
    }
}

/// What a block carries over to the next: the frame's output so far, the
/// repeat offsets, the last Huffman code and the last sequence tables.
pub struct FrameState {
    pub out: Seq<u8>,
    pub reps: Reps,
    pub huf: Option<HufCode>,
    pub seqt: Option<SeqTables>,
}

pub open spec fn initial_state() -> FrameState {
    FrameState { out: Seq::empty(), reps: Reps { r1: 1, r2: 4, r3: 8 }, huf: None, seqt: None }
}

/// The sequences section `b` of a block whose literals are `lits`.
#[verifier::opaque]
pub open spec fn seq_section(b: Seq<u8>, lits: Seq<u8>, window: nat, st: FrameState) -> Option<FrameState> {
    match nb_seq(b) {
        None => None,
        Some((n, h)) => if n == 0 {
            // No sequences: the section ends here, and the tables and
            // repeat offsets are unchanged.
            if h != b.len() {
                None
            } else {
                Some(FrameState { out: st.out + lits, ..st })
            }
        } else if h + 1 > b.len() || b[h] % 4 != 0 {
            None
        } else {
            let modes = b[h];
            let prev_ll = match st.seqt {
                None => None,
                Some(t) => Some(t.ll),
            };
            let prev_of = match st.seqt {
                None => None,
                Some(t) => Some(t.of),
            };
            let prev_ml = match st.seqt {
                None => None,
                Some(t) => Some(t.ml),
            };
            let a0 = h + 1;
            match seq_table(b.subrange(a0, b.len() as int), 0, (modes / 64) as nat, prev_ll) {
                None => None,
                Some((ll, u0)) => {
                    let a1 = a0 + u0;
                    match seq_table(b.subrange(a1, b.len() as int), 1, ((modes / 16) % 4) as nat, prev_of) {
                        None => None,
                        Some((of, u1)) => {
                            let a2 = a1 + u1;
                            match seq_table(b.subrange(a2, b.len() as int), 2, ((modes / 4) % 4) as nat, prev_ml) {
                                None => None,
                                Some((ml, u2)) => {
                                    let a3 = a2 + u2;
                                    let s = b.subrange(a3, b.len() as int);
                                    let t = SeqTables { ll: ll, of: of, ml: ml };
                                    match bstart(s) {
                                        None => None,
                                        Some(p) => if ll.log + of.log + ml.log > p {
                                            None
                                        } else {
                                            let sll = bits(s, p - ll.log, ll.log);
                                            let sof = bits(s, p - ll.log - of.log, of.log);
                                            let sml = bits(s, p - ll.log - of.log - ml.log, ml.log);
                                            let st0 = SeqState {
                                                p: p - ll.log - of.log - ml.log,
                                                sll: sll,
                                                sof: sof,
                                                sml: sml,
                                                reps: st.reps,
                                                li: 0,
                                                out: st.out,
                                            };
                                            match seq_run(t, s, lits, window, n, st0) {
                                                None => None,
                                                Some(fin) => if fin.p != 0 {
                                                    None
                                                } else {
                                                    Some(
                                                        FrameState {
                                                            out: fin.out + lits.subrange(fin.li, lits.len() as int),
                                                            reps: fin.reps,
                                                            huf: st.huf,
                                                            seqt: Some(t),
                                                        },
                                                    )
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

/// A compressed block's content `b` (§3.1.1.3): literals, then sequences.
/// It must decode to at most `bmax` bytes.
pub open spec fn compressed_block(b: Seq<u8>, window: nat, bmax: nat, st: FrameState) -> Option<FrameState> {
    match lit_section(b, bmax, st.huf) {
        None => None,
        Some(l) => match seq_section(
            b.subrange(l.used, b.len() as int),
            l.lits,
            window,
            FrameState { huf: l.huf, ..st },
        ) {
            None => None,
            Some(st2) => if st2.out.len() > st.out.len() + bmax {
                None
            } else {
                Some(st2)
            },
        },
    }
}

// ---------------------------------------------------------------------------
// XXH64 (the content checksum, §3.1.1), from verilith-xxhash
// ---------------------------------------------------------------------------

#[cfg(verus_only)]
pub use verilith_xxhash::spec::xxh64;

// ---------------------------------------------------------------------------
// Frames (§3.1.1)
// ---------------------------------------------------------------------------

pub spec const MAGIC: nat = 0xFD2FB528;

pub spec const BLOCK_MAX: nat = 131072;

/// A frame header, decoded.
pub struct Header {
    pub window: nat,
    pub fcs: Option<nat>,
    pub checksum: bool,
    pub dict_id: nat,
    pub size: int,
}

/// The frame header after the magic number, at the start of `b`.
/// Window logs above 31 are rejected (libzstd's limit on 64-bit hosts).
pub open spec fn frame_header(b: Seq<u8>) -> Option<Header> {
    if b.len() < 1 {
        None
    } else {
        let fhd = b[0];
        let did_flag = fhd % 4;
        let checksum = (fhd / 4) % 2 == 1;
        let reserved = (fhd / 8) % 2 == 1;
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
        let size = 1 + wd_size + did_size + fcs_size;
        if reserved || b.len() < size {
            None
        } else {
            let wlog = if single {
                0
            } else {
                b[1] / 8 + 10
            };
            let dict_id = le(b, 1 + wd_size, did_size as nat);
            let fcs_raw = le(b, 1 + wd_size + did_size, fcs_size as nat);
            let fcs: Option<nat> = if fcs_size == 0 {
                None
            } else if fcs_size == 2 {
                Some(fcs_raw + 256)
            } else {
                Some(fcs_raw)
            };
            if !single && wlog > 31 {
                None
            } else {
                let window = if single {
                    fcs.unwrap()
                } else {
                    pow2(wlog as nat) + (pow2(wlog as nat) / 8) * (b[1] % 8) as nat
                };
                Some(Header { window: window, fcs: fcs, checksum: checksum, dict_id: dict_id, size: size })
            }
        }
    }
}

/// The blocks of a frame from `i` on, until the last block. Returns the
/// position after the last block and the final state.
pub open spec fn blocks(b: Seq<u8>, i: int, window: nat, st: FrameState) -> Option<(int, FrameState)>
    decreases b.len() - i,
{
    if i < 0 || i + 3 > b.len() {
        None
    } else {
        let bh = le(b, i, 3);
        let last = bh % 2 == 1;
        let ty = (bh / 2) % 4;
        let size = bh / 8;
        let bmax = min(window as int, BLOCK_MAX as int) as nat;
        let c = i + 3;
        if size > bmax {
            None
        } else {
            let r: Option<(int, FrameState)> = if ty == 0 {
                if c + size > b.len() {
                    None
                } else {
                    Some((c + size, FrameState { out: st.out + b.subrange(c, c + size), ..st }))
                }
            } else if ty == 1 {
                if c + 1 > b.len() {
                    None
                } else {
                    Some((c + 1, FrameState { out: st.out + Seq::new(size, |k: int| b[c]), ..st }))
                }
            } else if ty == 2 {
                if c + size > b.len() {
                    None
                } else {
                    match compressed_block(b.subrange(c, c + size), window, bmax, st) {
                        None => None,
                        Some(st2) => Some((c + size, st2)),
                    }
                }
            } else {
                None
            };
            match r {
                None => None,
                Some((j, st2)) => if last {
                    Some((j, st2))
                } else {
                    blocks(b, j, window, st2)
                },
            }
        }
    }
}

/// One Zstandard frame at `i` (after its magic number is checked).
/// Returns the position after it and its content. Frames that name a
/// dictionary are rejected: no dictionary is loaded.
pub open spec fn frame(b: Seq<u8>, i: int) -> Option<(int, Seq<u8>)> {
    match frame_header(b.subrange(i + 4, b.len() as int)) {
        None => None,
        Some(h) => if h.dict_id != 0 {
            None
        } else {
            match blocks(b, i + 4 + h.size, h.window, initial_state()) {
                None => None,
                Some((j, st)) => {
                    let out = st.out;
                    if h.fcs is Some && h.fcs.unwrap() != out.len() {
                        None
                    } else if h.checksum {
                        if j + 4 > b.len() || le(b, j, 4) != xxh64(out) as nat % 0x1_0000_0000 {
                            None
                        } else {
                            Some((j + 4, out))
                        }
                    } else {
                        Some((j, out))
                    }
                },
            }
        },
    }
}

/// Is the 4-byte number a skippable frame's magic (0x184D2A50..5F)?
pub open spec fn skippable(m: nat) -> bool {
    m / 16 == 0x184D2A5
}

/// Decompresses the frames from `i` on, appending to `out` (§3.1):
/// Zstandard frames and skippable frames, one after another. Fewer than 5
/// bytes left over is an error (libzstd's rule), as is anything that is
/// not a frame.
#[verifier::rlimit(100)]
pub open spec fn frames(b: Seq<u8>, i: int, out: Seq<u8>) -> Option<Seq<u8>>
    decreases b.len() - i,
{
    if i < 0 || i > b.len() {
        None
    } else if i == b.len() {
        Some(out)
    } else if i + 5 > b.len() {
        None
    } else {
        let m = le(b, i, 4);
        if skippable(m) {
            if i + 8 > b.len() {
                None
            } else {
                let size = le(b, i + 4, 4);
                if size + 8 >= 0x1_0000_0000 || i + 8 + size > b.len() {
                    None
                } else {
                    frames(b, i + 8 + size, out)
                }
            }
        } else if m != MAGIC {
            None
        } else {
            match frame(b, i) {
                None => None,
                Some((j, o)) => if j <= i || j > b.len() {
                    None
                } else {
                    frames(b, j, out + o)
                },
            }
        }
    }
}

/// The decompression of `b`, or `None` if it is not valid.
pub open spec fn decompress(b: Seq<u8>) -> Option<Seq<u8>> {
    frames(b, 0, Seq::empty())
}

} // verus!
