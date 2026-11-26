//! The specification: RFC 7541 (HPACK) decoding as pure functions, with
//! the limits and the header-block rules of nghttp2's inflater, which vhpack
//! replaces. Everything here is trusted: it is what the proofs prove the
//! code computes.
//!
//! - Integers (§5.1), with nghttp2's bounds: at most five continuation
//!   bytes, and the value fits in 32 bits.
//! - Huffman-coded strings (§5.2, Appendix B): the code is RFC 7541's
//!   table (`hcode`, `hlen`, from `htables.rs`); a string is the symbols of
//!   its codes followed by fewer than 8 bits of padding that are the start
//!   of EOS (all ones). EOS itself is an error.
//! - String literals (§5.2) of at most 65536 bytes (nghttp2's
//!   `NGHTTP2_HD_MAX_NV`).
//! - The static table (Appendix A, `static_entry`) and the dynamic table
//!   (§2.3.2, §4): entries newest first, each costing its name and value
//!   lengths plus 32, evicted oldest first to fit the maximum size.
//! - The field representations (§6) and dynamic table size updates (§6.3),
//!   which are allowed only at the start of a header block and must not
//!   exceed the limit the decoder announced (SETTINGS_HEADER_TABLE_SIZE);
//!   after the limit is lowered, the next block must start with an update
//!   no larger than the lowest limit announced in between (§4.2).
use crate::htables::*;
use vstd::prelude::*;

verus! {

/// Largest string literal length (nghttp2's `NGHTTP2_HD_MAX_NV`).
pub const MAX_STR: u32 = 65536;

/// Entries in the static table.
pub const STATIC_LEN: u32 = 61;

/// `UINT32_MAX`: nghttp2's "no pending table size limit".
pub const NO_LIMIT: u32 = 0xFFFF_FFFF;

/// The per-entry overhead of §4.1.
pub const ENTRY_OVERHEAD: u32 = 32;

// ---------------------------------------------------------------------------
// The tables (trusted data, see htables.rs and stable.rs)
// ---------------------------------------------------------------------------

/// The Huffman code of symbol `s` (0..=256, 256 being EOS), first bit most
/// significant, and its length in bits: RFC 7541 Appendix B (`htables.rs`).
pub open spec fn hcode(s: int) -> nat {
    HUFF_CODE@[s] as nat
}

pub open spec fn hlen(s: int) -> nat {
    HUFF_LEN@[s] as nat
}

/// Entry `i` (0-based) of the static table: RFC 7541 Appendix A.
pub uninterp spec fn static_name(i: int) -> Seq<u8>;

pub uninterp spec fn static_value(i: int) -> Seq<u8>;

// ---------------------------------------------------------------------------
// Bits, first bit most significant
// ---------------------------------------------------------------------------

/// Bit `k` of `b`, counting from the most significant bit of `b[0]`.
pub open spec fn bit(b: Seq<u8>, k: int) -> nat {
    ((b[k / 8] as nat) / pow2_8((7 - k % 8) as nat)) % 2
}

/// `2^n` for `n < 8`.
pub open spec fn pow2_8(n: nat) -> nat {
    if n == 0 { 1 } else if n == 1 { 2 } else if n == 2 { 4 } else if n == 3 { 8 }
    else if n == 4 { 16 } else if n == 5 { 32 } else if n == 6 { 64 } else { 128 }
}

/// The `n` bits of `b` from bit `p`, read as a number (first bit most
/// significant).
pub open spec fn code(b: Seq<u8>, p: int, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        2 * code(b, p, (n - 1) as nat) + bit(b, p + n - 1)
    }
}

// ---------------------------------------------------------------------------
// Integers (§5.1)
// ---------------------------------------------------------------------------

pub enum IntR {
    /// The input ends first.
    Short,
    Bad,
    /// The value and the position after it.
    Ok(nat, int),
}

/// An integer with an `n`-bit prefix at `b[pos]` (§5.1).
pub open spec fn int_dec(b: Seq<u8>, pos: int, n: nat) -> IntR {
    if pos < 0 || pos >= b.len() {
        IntR::Short
    } else {
        let k = (pow2_8(n) - 1) as nat; // 2^n - 1, for 4 <= n <= 7
        let first = (b[pos] as nat) % pow2_8(n);
        if first < k {
            IntR::Ok(first, pos + 1)
        } else {
            int_tail(b, pos + 1, 0, k)
        }
    }
}

/// The continuation bytes from `b[pos]`, the `i`-th one adding its low 7
/// bits times `2^(7i)` to `acc`. Like nghttp2, a sixth byte (shift 35) or a
/// value above `u32::MAX` is an error.
pub open spec fn int_tail(b: Seq<u8>, pos: int, i: nat, acc: nat) -> IntR
    decreases 5 - i,
{
    if pos < 0 || pos >= b.len() {
        IntR::Short
    } else if i >= 5 {
        IntR::Bad
    } else {
        let add = ((b[pos] as nat) % 128) * pow128(i);
        if acc + add > 0xFFFF_FFFF {
            IntR::Bad
        } else if b[pos] < 128 {
            IntR::Ok(acc + add, pos + 1)
        } else {
            int_tail(b, pos + 1, i + 1, acc + add)
        }
    }
}

/// `128^i`.
pub open spec fn pow128(i: nat) -> nat
    decreases i,
{
    if i == 0 { 1 } else { 128 * pow128((i - 1) as nat) }
}

// ---------------------------------------------------------------------------
// Huffman (§5.2, Appendix B)
// ---------------------------------------------------------------------------

/// Some symbol's code has length `l` and value `v`.
pub open spec fn hmatch(l: nat, v: nat) -> bool {
    exists|s: int| 0 <= s < 257 && hlen(s) == l && hcode(s) == v
}

/// That symbol (the code is prefix-free, so there is at most one; see
/// tests/tables.rs).
pub open spec fn hsym(l: nat, v: nat) -> int {
    choose|s: int| 0 <= s < 257 && hlen(s) == l && hcode(s) == v
}

/// The shortest code, of length `l` or more and at most 30 bits and at most
/// `r`, matching the bits of `b` from `p`: its symbol and its length.
pub open spec fn hfind(b: Seq<u8>, p: int, r: nat, l: nat) -> Option<(int, nat)>
    decreases 31 - l,
{
    if l > 30 || l > r {
        None
    } else if hmatch(l, code(b, p, l)) {
        Some((hsym(l, code(b, p, l)), l))
    } else {
        hfind(b, p, r, l + 1)
    }
}

/// Decodes the bits of `b` from bit `p` to the end: the symbols, then at
/// most 7 bits of padding that are all ones (the start of EOS). `None` if
/// the bits are not of that form, or a code is EOS's.
pub open spec fn hdec(b: Seq<u8>, p: int) -> Option<Seq<u8>>
    decreases 8 * b.len() - p,
{
    let r = 8 * b.len() - p;
    if p < 0 || r <= 0 {
        Some(Seq::empty())
    } else {
        match hfind(b, p, r as nat, 1) {
            Some((s, l)) => {
                if s == 256 || l == 0 || l > r {
                    None
                } else {
                    match hdec(b, p + l) {
                        Some(t) => Some(seq![s as u8] + t),
                        None => None,
                    }
                }
            },
            None => {
                if r <= 7 && code(b, p, r as nat) + 1 == pow2_8(r as nat) {
                    Some(Seq::empty())
                } else {
                    None
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// String literals (§5.2)
// ---------------------------------------------------------------------------

pub enum StrR {
    Short,
    Bad,
    Ok(Seq<u8>, int),
}

/// A string literal at `b[pos]`: H bit, length (7-bit prefix), then that
/// many bytes, Huffman-coded if H is set.
pub open spec fn str_dec(b: Seq<u8>, pos: int) -> StrR {
    match int_dec(b, pos, 7) {
        IntR::Short => StrR::Short,
        IntR::Bad => StrR::Bad,
        IntR::Ok(n, e) => {
            if n > MAX_STR {
                StrR::Bad
            } else if e + n > b.len() {
                StrR::Short
            } else {
                let raw = b.subrange(e, e + n);
                if b[pos] >= 128 {
                    match hdec(raw, 0) {
                        Some(s) => StrR::Ok(s, e + n),
                        None => StrR::Bad,
                    }
                } else {
                    StrR::Ok(raw, e + n)
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The dynamic table (§2.3.2, §4)
// ---------------------------------------------------------------------------

pub type Entry = (Seq<u8>, Seq<u8>);

/// §4.1: an entry's size.
pub open spec fn esize(e: Entry) -> nat {
    e.0.len() + e.1.len() + 32
}

/// The size of a table (entries newest first).
pub open spec fn tsize(t: Seq<Entry>) -> nat
    decreases t.len(),
{
    if t.len() == 0 {
        0
    } else {
        tsize(t.drop_last()) + esize(t.last())
    }
}

/// Evicts the oldest entries until `room` more bytes fit in `max` (or the
/// table is empty).
pub open spec fn evict(t: Seq<Entry>, room: nat, max: nat) -> Seq<Entry>
    decreases t.len(),
{
    if t.len() > 0 && tsize(t) + room > max {
        evict(t.drop_last(), room, max)
    } else {
        t
    }
}

/// §4.4: adds an entry, evicting first; an entry larger than the maximum
/// empties the table and is not added.
pub open spec fn insert(t: Seq<Entry>, max: nat, e: Entry) -> Seq<Entry> {
    let t2 = evict(t, esize(e), max);
    if esize(e) > max {
        t2
    } else {
        seq![e] + t2
    }
}

/// Entry `i` of the index address space (§2.3.3): 1..=61 static, then the
/// dynamic table newest first.
pub open spec fn entry(t: Seq<Entry>, i: nat) -> Entry {
    if i <= 61 {
        (static_name(i - 1), static_value(i - 1))
    } else {
        t[i - 62]
    }
}

// ---------------------------------------------------------------------------
// Decoder state and field representations (§6)
// ---------------------------------------------------------------------------

/// What the decoder carries from one representation to the next.
pub struct DState {
    /// The dynamic table, newest first.
    pub table: Seq<Entry>,
    /// Its maximum size, set by the last size update.
    pub max: nat,
    /// The limit announced in SETTINGS_HEADER_TABLE_SIZE.
    pub settings: nat,
    /// The lowest limit announced since the last size update, or
    /// `NO_LIMIT`: an update must not exceed it (§4.2).
    pub pending: nat,
    /// At the start of a header block (no field decoded yet), where size
    /// updates are allowed.
    pub at_start: bool,
    /// The limit was lowered below `max`: the block must start with a
    /// size update.
    pub expect: bool,
}

/// A decoded header field.
pub struct Field {
    pub name: Seq<u8>,
    pub value: Seq<u8>,
    /// Literal Never Indexed (§6.2.3).
    pub never: bool,
}

pub enum Rep {
    /// The input ends inside the representation.
    Short,
    /// A decoding error (COMPRESSION_ERROR).
    Bad,
    /// A header field, the new state, and the representation's length.
    Field(Field, DState, int),
    /// A dynamic table size update, the new state, and its length.
    Update(DState, int),
}

pub open spec fn min(a: nat, b: nat) -> nat {
    if a < b { a } else { b }
}

/// The state after a field: no longer at the start of the block.
pub open spec fn after_field(st: DState, t: Seq<Entry>) -> DState {
    DState { table: t, at_start: false, ..st }
}

/// Decodes the representation at the start of `b`.
pub open spec fn rep(st: DState, b: Seq<u8>) -> Rep {
    if b.len() == 0 {
        Rep::Short
    } else {
        let c = b[0];
        if c & 0xE0 == 0x20 {
            // §6.3 Dynamic Table Size Update.
            if !st.at_start {
                Rep::Bad
            } else {
                match int_dec(b, 0, 5) {
                    IntR::Short => Rep::Short,
                    IntR::Bad => Rep::Bad,
                    IntR::Ok(v, e) => {
                        if v > min(st.pending, st.settings) {
                            Rep::Bad
                        } else {
                            Rep::Update(
                                DState {
                                    table: evict(st.table, 0, v),
                                    max: v,
                                    pending: NO_LIMIT as nat,
                                    expect: false,
                                    ..st
                                },
                                e,
                            )
                        }
                    },
                }
            }
        } else if st.expect {
            Rep::Bad
        } else if c >= 0x80 {
            // §6.1 Indexed Header Field.
            match int_dec(b, 0, 7) {
                IntR::Short => Rep::Short,
                IntR::Bad => Rep::Bad,
                IntR::Ok(i, e) => {
                    if i == 0 || i > st.table.len() + 61 {
                        Rep::Bad
                    } else {
                        let en = entry(st.table, i);
                        Rep::Field(
                            Field { name: en.0, value: en.1, never: false },
                            after_field(st, st.table),
                            e,
                        )
                    }
                },
            }
        } else {
            // §6.2 Literal Header Field: with incremental indexing (01),
            // without indexing (0000) or never indexed (0001).
            let incr = c & 0x40 != 0;
            let never = c & 0xF0 == 0x10;
            let newname = c == 0x40 || c == 0x00 || c == 0x10;
            let name_r: StrR = if newname {
                str_dec(b, 1)
            } else {
                match int_dec(b, 0, if incr { 6 } else { 4 }) {
                    IntR::Short => StrR::Short,
                    IntR::Bad => StrR::Bad,
                    IntR::Ok(i, e) => {
                        if i == 0 || i > st.table.len() + 61 {
                            StrR::Bad
                        } else {
                            StrR::Ok(entry(st.table, i).0, e)
                        }
                    },
                }
            };
            match name_r {
                StrR::Short => Rep::Short,
                StrR::Bad => Rep::Bad,
                StrR::Ok(name, e1) => match str_dec(b, e1) {
                    StrR::Short => Rep::Short,
                    StrR::Bad => Rep::Bad,
                    StrR::Ok(value, e2) => {
                        let t = if incr { insert(st.table, st.max, (name, value)) } else { st.table };
                        Rep::Field(Field { name, value, never }, after_field(st, t), e2)
                    },
                },
            }
        }
    }
}

/// The state after a header block (`nghttp2_hd_inflate_end_headers`,
/// which also drops an expected size update, as nghttp2 does).
pub open spec fn end_block(st: DState) -> DState {
    DState { at_start: true, expect: false, ..st }
}

/// `b` starts with whole size updates, `n` bytes of them, that take `st`
/// to the result. Each is decoded from the rest of `b`, as a decoder that
/// has all of `b` would.
pub open spec fn upd(st: DState, b: Seq<u8>, n: int) -> Option<DState>
    decreases n,
{
    if n < 0 {
        None
    } else if n == 0 {
        Some(st)
    } else {
        match rep(st, b) {
            Rep::Update(s2, e) => {
                if 0 < e <= n && e <= b.len() {
                    upd(s2, b.subrange(e, b.len() as int), n - e)
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// A whole header block `b` decoded from state `st`: its fields, in
/// order, and the state after its last representation. `None` if a
/// representation is invalid or the block ends inside one. This is what
/// `Decoder::feed` computes over a block, however it is split (each of its
/// steps is `rep`); the encoder is proven against it.
pub open spec fn block(st: DState, b: Seq<u8>) -> Option<(Seq<Field>, DState)>
    decreases b.len(),
{
    if b.len() == 0 {
        Some((Seq::empty(), st))
    } else {
        match rep(st, b) {
            Rep::Field(f, s2, e) => {
                if 0 < e <= b.len() {
                    match block(s2, b.subrange(e, b.len() as int)) {
                        Some((fs, s3)) => Some((seq![f] + fs, s3)),
                        None => None,
                    }
                } else {
                    None
                }
            },
            Rep::Update(s2, e) => {
                if 0 < e <= b.len() {
                    block(s2, b.subrange(e, b.len() as int))
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// SETTINGS_HEADER_TABLE_SIZE changed (`nghttp2_hd_inflate_change_table_size`):
/// if the new limit is below the current maximum, the table shrinks to it
/// and the next block must start with a size update no larger than it.
pub open spec fn change_settings(st: DState, n: nat) -> DState {
    if st.max > n {
        DState {
            settings: n,
            max: n,
            table: evict(st.table, 0, n),
            pending: n,
            expect: true,
            ..st
        }
    } else {
        DState { settings: n, ..st }
    }
}

/// The initial state: empty table of 4096 bytes (§6.5.2's default).
pub open spec fn initial() -> DState {
    DState {
        table: Seq::empty(),
        max: 4096,
        settings: 4096,
        pending: NO_LIMIT as nat,
        at_start: true,
        expect: false,
    }
}

} // verus!
