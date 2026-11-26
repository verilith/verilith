//! The specification: RFC 9204 (QPACK) as pure functions. Everything here is
//! trusted: it is what the proofs prove the code computes. Read it against
//! the RFC; section numbers below are RFC 9204's.
//!
//! - Prefixed integers (§4.1.1, RFC 7541 §5.1) with prefixes of 1 to 8
//!   bits. Values up to 2^62 - 1 are accepted, as §4.1.1 requires; larger
//!   values, and more than nine continuation bytes, are errors.
//! - String literals (§4.1.2) with an N-bit prefix (N = 4, 6 or 8 here),
//!   optionally Huffman-coded with RFC 7541's code, whose decoding is
//!   `verilith_hpack::spec::hdec`.
//! - The static table (Appendix A, `static_name`, `static_value`) and the
//!   dynamic table (§3.2): entries oldest first, with the count of entries
//!   evicted before them (`dropped`), so the entry with absolute index `a`
//!   (§3.2.4) is `ents[a - dropped]` and the Insert Count is
//!   `dropped + ents.len()`.
//! - Encoder instructions (§4.3) as the decoder applies them, and the
//!   encoder stream as a sequence of them (`erun`).
//! - Field sections (§4.5): the prefix with Required Insert Count (§4.5.1.1)
//!   and Base (§4.5.1.2), and the five field line representations.
//! - Decoder instructions (§4.4), as the decoder emits them and as the
//!   encoder applies them (`drun`).
//! - The decoder's blocked streams (§2.1.2, §2.2.1).
//!
//! Where the RFC leaves a choice to the implementation, the spec makes one,
//! and says so where it does.
use vstd::prelude::*;

verus! {

/// The largest integer accepted: 2^62 - 1 (§4.1.1).
pub const MAX_INT: u64 = 0x3FFF_FFFF_FFFF_FFFF;

/// Entries in the static table (Appendix A).
pub const STATIC_LEN: u64 = 99;

/// The per-entry overhead of §3.2.1.
pub const ENTRY_OVERHEAD: u64 = 32;

// ---------------------------------------------------------------------------
// Tables of constants
// ---------------------------------------------------------------------------

/// Entry `i` (0-based) of the static table: RFC 9204 Appendix A
/// (`stable.rs`, trusted data).
pub uninterp spec fn static_name(i: int) -> Seq<u8>;

pub uninterp spec fn static_value(i: int) -> Seq<u8>;

/// `2^n`.
pub open spec fn p2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * p2((n - 1) as nat)
    }
}

/// `128^i`.
pub open spec fn p128(i: nat) -> nat
    decreases i,
{
    if i == 0 {
        1
    } else {
        128 * p128((i - 1) as nat)
    }
}

// ---------------------------------------------------------------------------
// Prefixed integers (§4.1.1)
// ---------------------------------------------------------------------------

pub enum IntR {
    /// The input ends first.
    Short,
    Bad,
    /// The value and the position after it.
    Ok(nat, int),
}

/// An integer with an `n`-bit prefix (1 <= n <= 8) at `b[pos]`.
pub open spec fn int_dec(b: Seq<u8>, pos: int, n: nat) -> IntR {
    if pos < 0 || pos >= b.len() {
        IntR::Short
    } else {
        let k = (p2(n) - 1) as nat;
        let first = (b[pos] as nat) % p2(n);
        if first < k {
            IntR::Ok(first, pos + 1)
        } else {
            int_tail(b, pos + 1, 0, k)
        }
    }
}

/// The continuation bytes from `b[pos]`, the `i`-th one adding its low 7
/// bits times `128^i` to `acc`. A tenth byte, or a value above `MAX_INT`,
/// is an error (nine bytes carry 63 bits, more than any accepted value
/// needs).
pub open spec fn int_tail(b: Seq<u8>, pos: int, i: nat, acc: nat) -> IntR
    decreases 9 - i,
{
    if pos < 0 || pos >= b.len() {
        IntR::Short
    } else if i >= 9 {
        IntR::Bad
    } else {
        let acc2 = acc + ((b[pos] as nat) % 128) * p128(i);
        if acc2 > MAX_INT {
            IntR::Bad
        } else if b[pos] < 128 {
            IntR::Ok(acc2, pos + 1)
        } else {
            int_tail(b, pos + 1, i + 1, acc2)
        }
    }
}

/// The encoding of `v` with an `n`-bit prefix, the bits above the prefix
/// being `flags` (a multiple of `2^n`, below 256).
pub open spec fn int_enc(flags: nat, n: nat, v: nat) -> Seq<u8> {
    let k = (p2(n) - 1) as nat;
    if v < k {
        seq![(flags + v) as u8]
    } else {
        seq![(flags + k) as u8] + int_enc_tail((v - k) as nat)
    }
}

pub open spec fn int_enc_tail(v: nat) -> Seq<u8>
    decreases v,
{
    if v < 128 {
        seq![v as u8]
    } else {
        seq![(v % 128 + 128) as u8] + int_enc_tail(v / 128)
    }
}

// ---------------------------------------------------------------------------
// String literals (§4.1.2)
// ---------------------------------------------------------------------------

/// Where something that is only framed (not decoded) ends.
pub enum EndR {
    Short,
    Bad,
    Ok(int),
}

pub enum StrR {
    Short,
    Bad,
    Ok(Seq<u8>, int),
}

/// The H bit of an `n`-bit prefix string literal starting in byte `c`.
pub open spec fn hbit(c: u8, n: nat) -> bool {
    (c as nat) % p2(n) >= p2((n - 1) as nat)
}

/// The end of the `n`-bit prefix string literal at `b[pos]`: its length
/// (an `(n-1)`-bit prefix integer) and that many bytes. A length above
/// `limit` is an error.
pub open spec fn str_end(b: Seq<u8>, pos: int, n: nat, limit: nat) -> EndR {
    match int_dec(b, pos, (n - 1) as nat) {
        IntR::Short => EndR::Short,
        IntR::Bad => EndR::Bad,
        IntR::Ok(len, e) => {
            if len > limit {
                EndR::Bad
            } else if e + len > b.len() {
                EndR::Short
            } else {
                EndR::Ok(e + len)
            }
        },
    }
}

/// The `n`-bit prefix string literal at `b[pos]`, decoded.
pub open spec fn str_dec(b: Seq<u8>, pos: int, n: nat, limit: nat) -> StrR {
    match int_dec(b, pos, (n - 1) as nat) {
        IntR::Short => StrR::Short,
        IntR::Bad => StrR::Bad,
        IntR::Ok(len, e) => {
            if len > limit {
                StrR::Bad
            } else if e + len > b.len() {
                StrR::Short
            } else {
                let raw = b.subrange(e, e + len);
                if hbit(b[pos], n) {
                    match verilith_hpack::spec::hdec(raw, 0) {
                        Some(s) => StrR::Ok(s, e + len),
                        None => StrR::Bad,
                    }
                } else {
                    StrR::Ok(raw, e + len)
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The dynamic table (§3.2)
// ---------------------------------------------------------------------------

pub type Entry = (Seq<u8>, Seq<u8>);

/// §3.2.1: an entry's size.
pub open spec fn esize(e: Entry) -> nat {
    e.0.len() + e.1.len() + 32
}

/// The size of a sequence of entries.
pub open spec fn tsize(s: Seq<Entry>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        tsize(s.drop_last()) + esize(s.last())
    }
}

pub struct Table {
    /// The entries, oldest first.
    pub ents: Seq<Entry>,
    /// Entries evicted so far: `ents[0]` has absolute index `dropped`.
    pub dropped: nat,
    /// The capacity (§3.2.2), set by the encoder.
    pub cap: nat,
}

/// The Insert Count: entries inserted so far (§2.1.4, §3.2.4).
pub open spec fn icount(t: Table) -> nat {
    t.dropped + t.ents.len()
}

/// The initial table: empty, with capacity 0 (§3.2.2).
pub open spec fn empty_table() -> Table {
    Table { ents: Seq::empty(), dropped: 0, cap: 0 }
}

/// Evicts the oldest entries until `room` more bytes fit in `cap`, or the
/// table is empty (§3.2.2).
pub open spec fn evict(t: Table, room: nat, cap: nat) -> Table
    decreases t.ents.len(),
{
    if t.ents.len() > 0 && tsize(t.ents) + room > cap {
        evict(Table { ents: t.ents.drop_first(), dropped: t.dropped + 1, cap: t.cap }, room, cap)
    } else {
        t
    }
}

/// Adds an entry, evicting first. An entry larger than the capacity is an
/// error (§3.2.2), and so (the spec's own limit) is an insert past
/// `MAX_INT` inserts, which no Required Insert Count could refer to.
pub open spec fn insert(t: Table, e: Entry) -> Option<Table> {
    if esize(e) > t.cap || icount(t) >= MAX_INT {
        None
    } else {
        let t2 = evict(t, esize(e), t.cap);
        Some(Table { ents: t2.ents.push(e), ..t2 })
    }
}

/// Set Dynamic Table Capacity (§4.3.1), once checked against the maximum.
pub open spec fn set_cap(t: Table, c: nat) -> Table {
    let t2 = evict(t, 0, c);
    Table { cap: c, ..t2 }
}

/// The entry with relative index `r` in an encoder instruction (§3.2.5):
/// `r` counts back from the newest entry.
pub open spec fn rel_ok(t: Table, r: nat) -> bool {
    r < t.ents.len()
}

pub open spec fn rel(t: Table, r: nat) -> Entry {
    t.ents[t.ents.len() - 1 - r]
}

/// The entry with absolute index `a` (§3.2.4).
pub open spec fn abs_ok(t: Table, a: nat) -> bool {
    t.dropped <= a < icount(t)
}

pub open spec fn abs(t: Table, a: nat) -> Entry {
    t.ents[a - t.dropped]
}

/// The static entry `i`.
pub open spec fn sentry(i: nat) -> Entry {
    (static_name(i as int), static_value(i as int))
}

// ---------------------------------------------------------------------------
// Encoder instructions (§4.3) and the encoder stream
// ---------------------------------------------------------------------------

/// The longest string literal accepted on the encoder stream, for a
/// maximum table capacity `max_cap`. This is the spec's own limit, but it
/// rejects nothing the RFC allows: a string of `L` bytes decodes to at
/// least `(8L - 7) / 30` bytes (a Huffman code is at most 30 bits), so a
/// longer one could only make an entry larger than the capacity, which is
/// an error (§3.2.2). It bounds what a decoder must buffer.
pub open spec fn str_limit(max_cap: nat) -> nat {
    4 * max_cap + 8
}

/// The end of the encoder instruction at the start of `b`, from its
/// integers and string lengths alone (no string is decoded). A decoder
/// waits for a whole instruction before decoding any of it, so an error
/// inside one is reported once all of it has arrived.
#[verifier::opaque]
pub open spec fn eframe(b: Seq<u8>, max_cap: nat) -> EndR {
    let lim = str_limit(max_cap);
    if b.len() == 0 {
        EndR::Short
    } else if b[0] >= 0x80 {
        // Insert with Name Reference: 1 T Index(6+), Value.
        match int_dec(b, 0, 6) {
            IntR::Short => EndR::Short,
            IntR::Bad => EndR::Bad,
            IntR::Ok(_, e) => str_end(b, e, 8, lim),
        }
    } else if b[0] >= 0x40 {
        // Insert with Literal Name: 01 Name(6-bit prefix string), Value.
        match str_end(b, 0, 6, lim) {
            EndR::Ok(e) => str_end(b, e, 8, lim),
            r => r,
        }
    } else {
        // Set Dynamic Table Capacity (001) and Duplicate (000): an integer
        // with a 5-bit prefix.
        match int_dec(b, 0, 5) {
            IntR::Short => EndR::Short,
            IntR::Bad => EndR::Bad,
            IntR::Ok(_, e) => EndR::Ok(e),
        }
    }
}

/// Applies the encoder instruction `b` (all of it, as framed by `eframe`)
/// to the table. `None` is QPACK_ENCODER_STREAM_ERROR.
#[verifier::opaque]
pub open spec fn einst(t: Table, max_cap: nat, b: Seq<u8>) -> Option<Table> {
    let lim = str_limit(max_cap);
    if b.len() == 0 {
        None
    } else if b[0] >= 0x80 {
        // §4.3.2 Insert with Name Reference. T (0x40) selects the static
        // table; otherwise the index is relative (§3.2.5).
        match int_dec(b, 0, 6) {
            IntR::Ok(i, e) => {
                let name_ok = if b[0] >= 0xC0 { i < STATIC_LEN } else { rel_ok(t, i) };
                let name = if b[0] >= 0xC0 { static_name(i as int) } else { rel(t, i).0 };
                match str_dec(b, e, 8, lim) {
                    StrR::Ok(v, _) => if name_ok { insert(t, (name, v)) } else { None },
                    _ => None,
                }
            },
            _ => None,
        }
    } else if b[0] >= 0x40 {
        // §4.3.3 Insert with Literal Name.
        match str_dec(b, 0, 6, lim) {
            StrR::Ok(n, e) => match str_dec(b, e, 8, lim) {
                StrR::Ok(v, _) => insert(t, (n, v)),
                _ => None,
            },
            _ => None,
        }
    } else if b[0] >= 0x20 {
        // §4.3.1 Set Dynamic Table Capacity: at most the maximum.
        match int_dec(b, 0, 5) {
            IntR::Ok(c, _) => if c > max_cap { None } else { Some(set_cap(t, c)) },
            _ => None,
        }
    } else {
        // §4.3.4 Duplicate.
        match int_dec(b, 0, 5) {
            IntR::Ok(i, _) => if rel_ok(t, i) { insert(t, rel(t, i)) } else { None },
            _ => None,
        }
    }
}

pub enum Run<S> {
    /// An error.
    Bad,
    /// The state after the whole instructions at the start of the input,
    /// and how many bytes they take. What follows is the start of an
    /// instruction that has not fully arrived.
    Ok(S, int),
}

/// The encoder stream `b`, applied to `t` instruction by instruction.
pub open spec fn erun(t: Table, max_cap: nat, b: Seq<u8>) -> Run<Table>
    decreases b.len(),
{
    match eframe(b, max_cap) {
        EndR::Short => Run::Ok(t, 0),
        EndR::Bad => Run::Bad,
        EndR::Ok(e) => {
            if e <= 0 || e > b.len() {
                Run::Bad
            } else {
                match einst(t, max_cap, b.subrange(0, e)) {
                    None => Run::Bad,
                    Some(t2) => match erun(t2, max_cap, b.subrange(e, b.len() as int)) {
                        Run::Bad => Run::Bad,
                        Run::Ok(t3, k) => Run::Ok(t3, e + k),
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Field sections (§4.5)
// ---------------------------------------------------------------------------

/// A field line.
pub struct Field {
    pub name: Seq<u8>,
    pub value: Seq<u8>,
    /// The N bit (§4.5.4): the field must stay a literal on later hops.
    pub never: bool,
}

/// A field line's size as HTTP/3 counts it for
/// SETTINGS_MAX_FIELD_SECTION_SIZE (RFC 9114 §4.2.2).
pub open spec fn fsize(f: Field) -> nat {
    f.name.len() + f.value.len() + 32
}

/// MaxEntries (§4.5.1.1).
pub open spec fn max_entries(max_cap: nat) -> nat {
    max_cap / 32
}

/// Required Insert Count from its encoding (§4.5.1.1), `total` being the
/// decoder's Insert Count. `None` is an encoding no conformant encoder
/// produces.
pub open spec fn decode_ric(enc: nat, max_cap: nat, total: nat) -> Option<nat> {
    let me = max_entries(max_cap);
    let full = 2 * me;
    if enc == 0 {
        Some(0)
    } else if enc > full {
        None
    } else {
        let max_value = total + me;
        let max_wrapped = (max_value / full) * full;
        let ric = max_wrapped + enc - 1;
        if ric > max_value {
            if ric <= full {
                None
            } else {
                Some((ric - full) as nat)
            }
        } else if ric == 0 {
            None
        } else {
            Some(ric as nat)
        }
    }
}

/// The encoding of Required Insert Count `ric` (§4.5.1.1).
pub open spec fn encode_ric(ric: nat, max_cap: nat) -> nat {
    if ric == 0 {
        0
    } else {
        ric % (2 * max_entries(max_cap)) + 1
    }
}

/// A dynamic table reference from a field line, by absolute index: it
/// must be below the Required Insert Count and not yet evicted (§2.2.3).
/// (`ric <= icount(t)` whenever lines are decoded, so the entry exists.)
pub open spec fn dref_ok(t: Table, ric: nat, a: int) -> bool {
    0 <= a && a < ric && t.dropped <= a && a < icount(t)
}

/// The field line representation at `b[pos]`, and where it ends. `None`
/// is QPACK_DECOMPRESSION_FAILED (the section is whole, so a
/// representation cut short is an error too).
#[verifier::opaque]
pub open spec fn line(t: Table, ric: nat, base: nat, b: Seq<u8>, pos: int) -> Option<(Field, int)> {
    let lim = b.len() as nat;
    let c = b[pos];
    if c >= 0x80 {
        // §4.5.2 Indexed Field Line: 1 T Index(6+).
        match int_dec(b, pos, 6) {
            IntR::Ok(i, e) => {
                if c >= 0xC0 {
                    if i < STATIC_LEN {
                        Some((Field { name: static_name(i as int), value: static_value(i as int), never: false }, e))
                    } else {
                        None
                    }
                } else {
                    let a = base - 1 - i;
                    if dref_ok(t, ric, a) {
                        let en = abs(t, a as nat);
                        Some((Field { name: en.0, value: en.1, never: false }, e))
                    } else {
                        None
                    }
                }
            },
            _ => None,
        }
    } else if c >= 0x40 {
        // §4.5.4 Literal Field Line with Name Reference: 01 N T Index(4+).
        match int_dec(b, pos, 4) {
            IntR::Ok(i, e) => {
                let never = (c as nat) % 64 >= 32;
                let stat = (c as nat) % 32 >= 16;
                let a = base - 1 - i;
                let name_ok = if stat { i < STATIC_LEN } else { dref_ok(t, ric, a) };
                let name = if stat { static_name(i as int) } else { abs(t, a as nat).0 };
                match str_dec(b, e, 8, lim) {
                    StrR::Ok(v, e2) => if name_ok { Some((Field { name, value: v, never }, e2)) } else { None },
                    _ => None,
                }
            },
            _ => None,
        }
    } else if c >= 0x20 {
        // §4.5.6 Literal Field Line with Literal Name: 001 N Name(4-bit
        // prefix string), Value.
        let never = (c as nat) % 32 >= 16;
        match str_dec(b, pos, 4, lim) {
            StrR::Ok(n, e) => match str_dec(b, e, 8, lim) {
                StrR::Ok(v, e2) => Some((Field { name: n, value: v, never }, e2)),
                _ => None,
            },
            _ => None,
        }
    } else if c >= 0x10 {
        // §4.5.3 Indexed Field Line with Post-Base Index: 0001 Index(4+).
        match int_dec(b, pos, 4) {
            IntR::Ok(i, e) => {
                let a = (base + i) as int;
                if dref_ok(t, ric, a) {
                    let en = abs(t, a as nat);
                    Some((Field { name: en.0, value: en.1, never: false }, e))
                } else {
                    None
                }
            },
            _ => None,
        }
    } else {
        // §4.5.5 Literal Field Line with Post-Base Name Reference:
        // 0000 N NameIndex(3+).
        match int_dec(b, pos, 3) {
            IntR::Ok(i, e) => {
                let never = (c as nat) % 16 >= 8;
                let a = (base + i) as int;
                match str_dec(b, e, 8, lim) {
                    StrR::Ok(v, e2) => if dref_ok(t, ric, a) {
                        Some((Field { name: abs(t, a as nat).0, value: v, never }, e2))
                    } else {
                        None
                    },
                    _ => None,
                }
            },
            _ => None,
        }
    }
}

pub enum SecR {
    /// QPACK_DECOMPRESSION_FAILED.
    Bad,
    /// The Required Insert Count is above the decoder's Insert Count: the
    /// stream is blocked until it is reached (§2.1.2).
    Blocked(nat),
    /// The field lines add up to more than the limit (the decoder's
    /// SETTINGS_MAX_FIELD_SECTION_SIZE, RFC 9114 §4.2.2).
    TooBig,
    /// The field lines, and the Required Insert Count.
    Ok(Seq<Field>, nat),
}

/// The field lines from `b[pos]` to the end, after `acc` whose sizes add
/// up to `size`, in order: the first error or excess decides.
pub open spec fn lines(t: Table, ric: nat, base: nat, max_size: nat, b: Seq<u8>, pos: int, size: nat, acc: Seq<Field>) -> SecR
    decreases b.len() - pos,
{
    if pos < 0 || pos >= b.len() {
        SecR::Ok(acc, ric)
    } else {
        match line(t, ric, base, b, pos) {
            None => SecR::Bad,
            Some((f, e)) => {
                if e <= pos || e > b.len() {
                    SecR::Bad
                } else if size + fsize(f) > max_size {
                    SecR::TooBig
                } else {
                    lines(t, ric, base, max_size, b, e, size + fsize(f), acc.push(f))
                }
            },
        }
    }
}

/// The encoded field section `b` (§4.5.1): the prefix, then field lines.
/// A Sign bit of 1 with Delta Base at least the Required Insert Count (a
/// negative Base) is an error (§4.5.1.2).
pub open spec fn section(t: Table, max_cap: nat, max_size: nat, b: Seq<u8>) -> SecR {
    match int_dec(b, 0, 8) {
        IntR::Ok(enc, e1) => match decode_ric(enc, max_cap, icount(t)) {
            None => SecR::Bad,
            Some(ric) => match int_dec(b, e1, 7) {
                IntR::Ok(delta, e2) => {
                    let sign = b[e1] >= 0x80;
                    if sign && ric <= delta {
                        SecR::Bad
                    } else if ric > icount(t) {
                        SecR::Blocked(ric)
                    } else {
                        let base = if sign { (ric - delta - 1) as nat } else { ric + delta };
                        lines(t, ric, base, max_size, b, e2, 0, Seq::empty())
                    }
                },
                _ => SecR::Bad,
            },
        },
        _ => SecR::Bad,
    }
}

// ---------------------------------------------------------------------------
// Decoder instructions (§4.4)
// ---------------------------------------------------------------------------

/// Section Acknowledgment (§4.4.1).
pub open spec fn section_ack(stream: nat) -> Seq<u8> {
    int_enc(0x80, 7, stream)
}

/// Stream Cancellation (§4.4.2).
pub open spec fn stream_cancel(stream: nat) -> Seq<u8> {
    int_enc(0x40, 6, stream)
}

/// Insert Count Increment (§4.4.3).
pub open spec fn insert_count_inc(n: nat) -> Seq<u8> {
    int_enc(0x00, 6, n)
}

// ---------------------------------------------------------------------------
// The decoder
// ---------------------------------------------------------------------------

/// What a decoder carries between calls.
pub struct DecState {
    pub table: Table,
    /// SETTINGS_QPACK_MAX_TABLE_CAPACITY, as this decoder sent it.
    pub max_cap: nat,
    /// SETTINGS_QPACK_BLOCKED_STREAMS, as this decoder sent it.
    pub max_blocked: nat,
    /// SETTINGS_MAX_FIELD_SECTION_SIZE, as this decoder sent it.
    pub max_size: nat,
    /// The blocked streams and the Required Insert Count each waits for,
    /// in the order they blocked; no stream appears twice.
    pub blocked: Seq<(nat, nat)>,
    /// The Insert Count the encoder knows this decoder has (its Known
    /// Received Count, §2.1.4) from the instructions emitted so far.
    pub acked: nat,
    /// The decoder stream: the instructions emitted so far, not yet taken.
    pub out: Seq<u8>,
}

pub open spec fn has_stream(bl: Seq<(nat, nat)>, s: nat) -> bool {
    exists|i: int| 0 <= i < bl.len() && #[trigger] bl[i].0 == s
}

/// `bl` without stream `s`.
pub open spec fn without(bl: Seq<(nat, nat)>, s: nat) -> Seq<(nat, nat)>
    decreases bl.len(),
{
    if bl.len() == 0 {
        bl
    } else {
        let r = without(bl.drop_last(), s);
        if bl.last().0 != s { r.push(bl.last()) } else { r }
    }
}

pub open spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

/// What decoding a field section did.
pub enum Decoded {
    /// The field lines.
    Done(Seq<Field>),
    /// The stream waits for more of the encoder stream: decode the same
    /// section again once the decoder reports the stream unblocked.
    Blocked,
    /// The section is over the size limit; the stream should be answered
    /// with an error (or reset, with `cancel`). The decoder is unchanged.
    TooBig,
    /// QPACK_DECOMPRESSION_FAILED, a connection error: the decoder must not
    /// be used again.
    Bad,
}

/// Decoding the field section `b` from stream `stream` (§2.2): the result
/// and the decoder state after it.
///
/// - A blocked stream is remembered; one more than `max_blocked` is an
///   error (§2.1.2).
/// - A decoded section with a Required Insert Count above 0 is
///   acknowledged on the decoder stream (§4.4.1), which also tells the
///   encoder the decoder has that many entries (§2.1.4).
pub open spec fn dec_section(st: DecState, stream: nat, b: Seq<u8>) -> (Decoded, DecState) {
    match section(st.table, st.max_cap, st.max_size, b) {
        SecR::Bad => (Decoded::Bad, st),
        SecR::TooBig => (Decoded::TooBig, st),
        SecR::Blocked(ric) => {
            if has_stream(st.blocked, stream) {
                (Decoded::Blocked, st)
            } else if st.blocked.len() >= st.max_blocked {
                (Decoded::Bad, st)
            } else {
                (Decoded::Blocked, DecState { blocked: st.blocked.push((stream, ric)), ..st })
            }
        },
        SecR::Ok(fields, ric) => {
            let st2 = DecState { blocked: without(st.blocked, stream), ..st };
            if ric == 0 {
                (Decoded::Done(fields), st2)
            } else {
                (Decoded::Done(fields), DecState { out: st2.out + section_ack(stream), acked: max(st2.acked, ric), ..st2 })
            }
        },
    }
}

/// After the encoder stream advanced the table: the streams it unblocked
/// (Required Insert Count reached), in the order they blocked.
pub open spec fn unblocked(bl: Seq<(nat, nat)>, count: nat) -> Seq<(nat, nat)>
    decreases bl.len(),
{
    if bl.len() == 0 {
        bl
    } else {
        let r = unblocked(bl.drop_last(), count);
        if bl.last().1 <= count { r.push(bl.last()) } else { r }
    }
}

pub open spec fn still_blocked(bl: Seq<(nat, nat)>, count: nat) -> Seq<(nat, nat)>
    decreases bl.len(),
{
    if bl.len() == 0 {
        bl
    } else {
        let r = still_blocked(bl.drop_last(), count);
        if bl.last().1 > count { r.push(bl.last()) } else { r }
    }
}

/// The decoder state after the encoder stream bytes `input`, with `held`
/// the start of an instruction left from before: the table after every
/// whole instruction in `held + input`, those streams unblocked, and an
/// Insert Count Increment (§4.4.3) for the new entries the encoder has not
/// yet heard of. `None` is QPACK_ENCODER_STREAM_ERROR. The second result
/// is what is left of `held + input` to keep for next time.
pub open spec fn dec_feed(st: DecState, held: Seq<u8>, input: Seq<u8>) -> Option<(DecState, Seq<u8>)> {
    let all = held + input;
    match erun(st.table, st.max_cap, all) {
        Run::Bad => None,
        Run::Ok(t, k) => {
            let n = icount(t);
            let st2 = DecState { table: t, blocked: still_blocked(st.blocked, n), ..st };
            let st3 = if n > st.acked {
                DecState { out: st2.out + insert_count_inc((n - st.acked) as nat), acked: n, ..st2 }
            } else {
                st2
            };
            Some((st3, all.subrange(k, all.len() as int)))
        },
    }
}

/// A stream was reset or abandoned (§2.2.2): it is no longer blocked, and
/// a Stream Cancellation tells the encoder (unless the dynamic table is
/// disabled, when it may be omitted, §4.4.2).
pub open spec fn dec_cancel(st: DecState, stream: nat) -> DecState {
    let st2 = DecState { blocked: without(st.blocked, stream), ..st };
    if st.max_cap == 0 {
        st2
    } else {
        DecState { out: st2.out + stream_cancel(stream), ..st2 }
    }
}

// ---------------------------------------------------------------------------
// The encoder's side of the decoder stream (§4.4)
// ---------------------------------------------------------------------------

/// A field section the encoder sent with dynamic table references, not yet
/// acknowledged (§2.1.1).
pub struct Sent {
    pub stream: nat,
    /// Its Required Insert Count (above 0).
    pub ric: nat,
    /// The lowest absolute index it references.
    pub min_ref: nat,
}

/// What the encoder knows of the decoder.
pub struct EncState {
    pub table: Table,
    /// The decoder's SETTINGS_QPACK_MAX_TABLE_CAPACITY.
    pub max_cap: nat,
    /// The decoder's SETTINGS_QPACK_BLOCKED_STREAMS.
    pub max_blocked: nat,
    /// The Known Received Count (§2.1.4).
    pub krc: nat,
    /// The sections not yet acknowledged, oldest first.
    pub sent: Seq<Sent>,
}

/// The decoder instruction at the start of `b`: one integer, with a 7-bit
/// prefix (Section Acknowledgment, 1...) or a 6-bit one (01... and 00...).
#[verifier::opaque]
pub open spec fn dframe(b: Seq<u8>) -> EndR {
    if b.len() == 0 {
        EndR::Short
    } else {
        match int_dec(b, 0, if b[0] >= 0x80 { 7 } else { 6 }) {
            IntR::Short => EndR::Short,
            IntR::Bad => EndR::Bad,
            IntR::Ok(_, e) => EndR::Ok(e),
        }
    }
}

/// The first unacknowledged section of stream `s`.
pub open spec fn first_of(sent: Seq<Sent>, s: nat) -> Option<int> {
    if exists|i: int| 0 <= i < sent.len() && #[trigger] sent[i].stream == s {
        Some(choose|i: int| 0 <= i < sent.len() && #[trigger] sent[i].stream == s
            && forall|j: int| 0 <= j < i ==> #[trigger] sent[j].stream != s)
    } else {
        None
    }
}

/// `sent` without the sections of stream `s`.
pub open spec fn drop_stream(sent: Seq<Sent>, s: nat) -> Seq<Sent>
    decreases sent.len(),
{
    if sent.len() == 0 {
        sent
    } else {
        let r = drop_stream(sent.drop_last(), s);
        if sent.last().stream != s { r.push(sent.last()) } else { r }
    }
}

/// Applies the decoder instruction `b` (all of it) on the encoder's side.
/// `None` is QPACK_DECODER_STREAM_ERROR.
#[verifier::opaque]
pub open spec fn dinst(st: EncState, b: Seq<u8>) -> Option<EncState> {
    if b.len() == 0 {
        None
    } else if b[0] >= 0x80 {
        // §4.4.1 Section Acknowledgment: the earliest unacknowledged
        // section of the stream; there must be one.
        match int_dec(b, 0, 7) {
            IntR::Ok(s, _) => match first_of(st.sent, s) {
                Some(i) => Some(EncState {
                    krc: max(st.krc, st.sent[i].ric),
                    sent: st.sent.remove(i),
                    ..st
                }),
                None => None,
            },
            _ => None,
        }
    } else if b[0] >= 0x40 {
        // §4.4.2 Stream Cancellation.
        match int_dec(b, 0, 6) {
            IntR::Ok(s, _) => Some(EncState { sent: drop_stream(st.sent, s), ..st }),
            _ => None,
        }
    } else {
        // §4.4.3 Insert Count Increment: not 0, and not past what was sent.
        match int_dec(b, 0, 6) {
            IntR::Ok(n, _) => {
                if n == 0 || st.krc + n > icount(st.table) {
                    None
                } else {
                    Some(EncState { krc: st.krc + n, ..st })
                }
            },
            _ => None,
        }
    }
}

/// The decoder stream `b`, applied instruction by instruction.
pub open spec fn drun(st: EncState, b: Seq<u8>) -> Run<EncState>
    decreases b.len(),
{
    match dframe(b) {
        EndR::Short => Run::Ok(st, 0),
        EndR::Bad => Run::Bad,
        EndR::Ok(e) => {
            if e <= 0 || e > b.len() {
                Run::Bad
            } else {
                match dinst(st, b.subrange(0, e)) {
                    None => Run::Bad,
                    Some(s2) => match drun(s2, b.subrange(e, b.len() as int)) {
                        Run::Bad => Run::Bad,
                        Run::Ok(s3, k) => Run::Ok(s3, e + k),
                    },
                }
            }
        },
    }
}

/// The encoder's obligations to the decoder (§2.1.1, §2.1.2, §3.2.3), which
/// the encoder is proven to keep at all times:
///
/// - the capacity is within the decoder's maximum;
/// - no entry the decoder has not acknowledged has been evicted
///   (`dropped <= krc`), and no entry an unacknowledged section references;
/// - at most `max_blocked` streams have a section that could block (its
///   Required Insert Count above the Known Received Count).
pub open spec fn enc_ok(st: EncState) -> bool {
    &&& st.table.cap <= st.max_cap
    &&& st.krc <= icount(st.table)
    &&& st.table.dropped <= st.krc
    &&& forall|i: int| 0 <= i < st.sent.len() ==> st.table.dropped <= #[trigger] st.sent[i].min_ref
    &&& forall|i: int| 0 <= i < st.sent.len() ==> 0 < #[trigger] st.sent[i].ric <= icount(st.table)
    &&& exists|ss: Seq<nat>| ss.len() <= st.max_blocked && #[trigger] covers(ss, st.sent, st.krc)
}

/// `ss` lists every stream with a section that could block.
pub open spec fn covers(ss: Seq<nat>, sent: Seq<Sent>, krc: nat) -> bool {
    forall|i: int| 0 <= i < sent.len() && #[trigger] sent[i].ric > krc ==> ss.contains(sent[i].stream)
}

} // verus!
