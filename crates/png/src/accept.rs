//! The decisions the libpng API (`src/libpng/`) makes about the chunks it
//! hands to the decoder, proven here rather than taken on trust.
//!
//! The libpng API reads the chunks itself, through the caller's I/O
//! functions, and handles each one as libpng 1.6.59 does: it checks the
//! CRC as the caller's `png_set_crc_action` asks, and decides whether IHDR,
//! PLTE and tRNS are accepted, ignored or an error. It then gives the
//! decoder a file made of the chunks it accepted, each written again with a
//! correct CRC. Those decisions, and the writing of that file, are the
//! functions below; the unverified code around them does only what they
//! say (reporting the warning or error each one names, storing the values
//! for the `png_get_*` functions).
//!
//! What is proven, for each decision:
//!
//! - the result as a function of the inputs (libpng's rules, which the
//!   `ensures` clauses spell out);
//! - for libpng's default settings (CRC actions not changed, benign errors
//!   reported as warnings), agreement with the specification's chunk walk
//!   (`spec::step`): a chunk before the image data is an error exactly when
//!   the specification rejects the file at it, and the palette and
//!   transparency handed to the decoder are exactly the ones the
//!   specification takes (`theorem_plte`, `theorem_trns`, `theorem_crc`,
//!   `ihdr_problems`);
//! - that a chunk written for the decoder (`put_chunk`) is read back by the
//!   specification as that chunk, with a correct CRC.
//!
//! What these theorems assume about the unverified caller is that the
//! `Seen` it passes describes the chunks it has accepted so far, which is
//! what `spec::Walk` records (`Seen::matches`).
use vstd::prelude::*;
use crate::spec::*;
use crate::chunks::read_be32;
#[cfg(verus_only)]
use verilith_zlib::spec as z;
#[cfg(verus_only)]
use verilith_zlib::checksum::{crc_from, lemma_crc_append, lemma_crc_from};

verus! {

// ---------------------------------------------------------------------------
// CRC actions (`png_set_crc_action`, `png_crc_error`,
// `png_crc_finish_critical`)
// ---------------------------------------------------------------------------

/// `PNG_FLAG_CRC_ANCILLARY_USE`, `..._NOWARN`, `PNG_FLAG_CRC_CRITICAL_USE`
/// and `..._IGNORE`, as bits of the flags `png_set_crc_action` sets.
pub const CRC_ANC_USE: u32 = 1;
pub const CRC_ANC_NOWARN: u32 = 2;
pub const CRC_CRIT_USE: u32 = 4;
pub const CRC_CRIT_IGNORE: u32 = 8;

/// What happens to a chunk once its CRC has been checked.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum CrcVerdict {
    /// The CRC is correct, or the caller asked for it not to be checked.
    Pass,
    /// The CRC is wrong: a warning ("CRC error"), and the chunk is
    /// discarded (an ancillary chunk) or used anyway (a critical chunk the
    /// caller asked to use).
    Warn,
    /// The CRC is wrong: an error ("CRC error").
    Fail,
}

/// Whether the CRC is checked as an ancillary chunk's: libpng's
/// `handle_as_ancillary`, which `PNG_FLAG_CRC_CRITICAL_IGNORE` overrides.
pub open spec fn as_ancillary(flags: u32, critical: bool, as_anc: bool) -> bool {
    (as_anc && flags & CRC_CRIT_IGNORE == 0) || !critical
}

/// libpng's verdict on a chunk's CRC (`png_crc_error` and
/// `png_crc_finish_critical`). `critical`: the chunk type is critical;
/// `as_anc`: the handler asks for the CRC to be treated as an ancillary
/// chunk's (PLTE in an image without a palette, IEND).
pub open spec fn crc_rule(flags: u32, critical: bool, as_anc: bool, crc_ok: bool) -> CrcVerdict {
    let anc = as_ancillary(flags, critical, as_anc);
    let need = if anc {
        flags & (CRC_ANC_USE | CRC_ANC_NOWARN) != CRC_ANC_USE | CRC_ANC_NOWARN
    } else {
        flags & CRC_CRIT_IGNORE == 0
    };
    if !need || crc_ok {
        CrcVerdict::Pass
    } else if if anc {
        flags & CRC_ANC_NOWARN == 0
    } else {
        flags & CRC_CRIT_USE != 0
    } {
        CrcVerdict::Warn
    } else {
        CrcVerdict::Fail
    }
}

/// `crc_rule`.
pub fn crc_verdict(flags: u32, critical: bool, as_anc: bool, crc_ok: bool) -> (r: CrcVerdict)
    ensures
        r == crc_rule(flags, critical, as_anc, crc_ok),
        // A correct CRC always passes.
        crc_ok ==> r == CrcVerdict::Pass,
        // A wrong one passes only when the caller turned the check off.
        !crc_ok && r == CrcVerdict::Pass ==> if as_ancillary(flags, critical, as_anc) {
            flags & (CRC_ANC_USE | CRC_ANC_NOWARN) == CRC_ANC_USE | CRC_ANC_NOWARN
        } else {
            flags & CRC_CRIT_IGNORE != 0
        },
        // With the default flags, a wrong CRC is an error in a critical
        // chunk and a warning (the chunk discarded) in an ancillary one.
        flags == 0 && !crc_ok ==> r == if as_ancillary(flags, critical, as_anc) {
            CrcVerdict::Warn
        } else {
            CrcVerdict::Fail
        },
{
    proof {
        lemma_flags0(critical, as_anc, crc_ok);
    }
    let anc = (as_anc && flags & CRC_CRIT_IGNORE == 0) || !critical;
    let need = if anc {
        flags & (CRC_ANC_USE | CRC_ANC_NOWARN) != CRC_ANC_USE | CRC_ANC_NOWARN
    } else {
        flags & CRC_CRIT_IGNORE == 0
    };
    if !need || crc_ok {
        CrcVerdict::Pass
    } else if if anc {
        flags & CRC_ANC_NOWARN == 0
    } else {
        flags & CRC_CRIT_USE != 0
    } {
        CrcVerdict::Warn
    } else {
        CrcVerdict::Fail
    }
}

/// `crc_rule` with the default flags.
pub proof fn lemma_flags0(critical: bool, as_anc: bool, crc_ok: bool)
    ensures
        as_ancillary(0, critical, as_anc) == (as_anc || !critical),
        crc_rule(0, critical, as_anc, crc_ok) == if crc_ok {
            CrcVerdict::Pass
        } else if as_anc || !critical {
            CrcVerdict::Warn
        } else {
            CrcVerdict::Fail
        },
{
    assert(0u32 & 8u32 == 0u32 && 0u32 & 4u32 == 0u32 && 0u32 & 2u32 == 0u32 && 0u32 & (1u32 | 2u32) == 0u32
        && (1u32 | 2u32) == 3u32) by (bit_vector);
}

/// The CRC of a chunk of type `ty` and data `d`: the CRC-32 of the four
/// type bytes and the data (§5.3), as `spec::chunk_at` checks it.
pub fn chunk_crc(ty: u32, d: &[u8]) -> (r: u32)
    ensures
        r == z::crc32(be32_bytes(ty) + d@),
{
    let t = [(ty >> 24) as u8, (ty >> 16) as u8, (ty >> 8) as u8, ty as u8];
    let c1 = verilith_zlib::checksum::cpu::crc32_update(0xffff_ffff, &t);
    let c2 = verilith_zlib::checksum::cpu::crc32_update(c1, d);
    proof {
        assert(t@ =~= be32_bytes(ty));
        lemma_crc_append(0xffff_ffff, t@, d@);
        lemma_crc_from(t@ + d@);
    }
    !c2
}

/// The four big-endian bytes of `x`.
pub open spec fn be32_bytes(x: u32) -> Seq<u8> {
    seq![(x >> 24) as u8, (x >> 16) as u8, (x >> 8) as u8, x as u8]
}

proof fn lemma_be32_bytes(x: u32)
    ensures
        be32(be32_bytes(x), 0) == x as nat,
{
    let b = be32_bytes(x);
    let (b0, b1, b2, b3) = ((x >> 24) as u8, (x >> 16) as u8, (x >> 8) as u8, x as u8);
    assert(b[0] == b0 && b[1] == b1 && b[2] == b2 && b[3] == b3);
    assert(((b0 as u32 * 256 + b1 as u32) * 256 + b2 as u32) * 256 + b3 as u32 == x) by (bit_vector)
        requires
            b0 == (x >> 24) as u8,
            b1 == (x >> 16) as u8,
            b2 == (x >> 8) as u8,
            b3 == x as u8,
    ;
}

// ---------------------------------------------------------------------------
// The file the decoder is given
// ---------------------------------------------------------------------------

/// Whether `ty` may be a chunk type (`spec::chunk_at`'s rule: four letters,
/// the third uppercase).
pub open spec fn type_ok(ty: u32) -> bool {
    let b = be32_bytes(ty);
    is_letter(b[0]) && is_letter(b[1]) && 65 <= b[2] <= 90 && is_letter(b[3])
}

fn is_letter_u8(x: u8) -> (r: bool)
    ensures
        r == is_letter(x),
{
    (65 <= x && x <= 90) || (97 <= x && x <= 122)
}

/// Appends a chunk of type `ty` and data `d`, with its correct CRC, to
/// `file`. Returns false and leaves `file` alone if `ty` is not a chunk
/// type or `d` is longer than a chunk can be.
pub fn put_chunk(file: &mut Vec<u8>, ty: u32, d: &[u8]) -> (r: bool)
    ensures
        r == (type_ok(ty) && d@.len() <= MAX_LEN),
        !r ==> final(file)@ == old(file)@,
        r ==> {
            &&& final(file)@.len() == old(file)@.len() + 12 + d@.len()
            &&& final(file)@.subrange(0, old(file)@.len() as int) == old(file)@
            &&& chunk_at(final(file)@, old(file)@.len() as int) == Some(
                Chunk { len: d@.len(), ty: ty as nat, crc_ok: true },
            )
            &&& chunk_data(final(file)@, old(file)@.len() as int, d@.len()) == d@
        },
{
    let t = [(ty >> 24) as u8, (ty >> 16) as u8, (ty >> 8) as u8, ty as u8];
    proof {
        assert(t@ =~= be32_bytes(ty));
    }
    if !(is_letter_u8(t[0]) && is_letter_u8(t[1]) && 65 <= t[2] && t[2] <= 90 && is_letter_u8(t[3]))
        || d.len() > 0x7fff_ffff {
        return false;
    }
    let ghost f0 = file@;
    let n = d.len() as u32;
    let l = [(n >> 24) as u8, (n >> 16) as u8, (n >> 8) as u8, n as u8];
    let c = chunk_crc(ty, d);
    let cb = [(c >> 24) as u8, (c >> 16) as u8, (c >> 8) as u8, c as u8];
    proof {
        assert(l@ =~= be32_bytes(n));
        assert(cb@ =~= be32_bytes(c));
    }
    file.extend_from_slice(&l);
    file.extend_from_slice(&t);
    file.extend_from_slice(d);
    file.extend_from_slice(&cb);
    proof {
        let f = file@;
        let p = f0.len() as int;
        let len = d@.len();
        assert(f =~= f0 + be32_bytes(n) + be32_bytes(ty) + d@ + be32_bytes(c));
        assert(f.subrange(0, p) =~= f0);
        lemma_be32_bytes(n);
        lemma_be32_bytes(ty);
        lemma_be32_bytes(c);
        assert(f.subrange(p, p + 4) =~= be32_bytes(n));
        assert(f.subrange(p + 4, p + 8) =~= be32_bytes(ty));
        assert(f.subrange(p + 8 + len, p + 12 + len) =~= be32_bytes(c));
        assert(f.subrange(p + 4, p + 8 + len) =~= be32_bytes(ty) + d@);
        assert(chunk_data(f, p, len) =~= d@);
        assert(be32(f, p) == be32(be32_bytes(n), 0));
        assert(be32(f, p + 4) == be32(be32_bytes(ty), 0));
        assert(be32(f, p + 8 + len) == be32(be32_bytes(c), 0));
        assert(f[p + 4] == t[0] && f[p + 5] == t[1] && f[p + 6] == t[2] && f[p + 7] == t[3]);
    }
    true
}

// ---------------------------------------------------------------------------
// IHDR (`png_check_IHDR`)
// ---------------------------------------------------------------------------

/// The problems `png_check_IHDR` reports, in the order of its warnings:
/// width zero, too large, over the caller's limit; height zero, too large,
/// over the limit; bit depth; colour type; their combination; interlace,
/// compression and filter methods. IHDR is accepted when there are none.
pub fn ihdr_problems(d: &[u8], wmax: u32, hmax: u32) -> (r: [bool; 12])
    ensures
        (forall|j: int| 0 <= j < 12 ==> !#[trigger] r@[j]) <==> (parse_ihdr(d@) is Some && be32(d@, 0)
            <= wmax as nat && be32(d@, 4) <= hmax as nat),
{
    if d.len() != 13 {
        let r = [true, true, true, true, true, true, true, true, true, true, true, true];
        proof {
            assert(r@[0]);
        }
        return r;
    }
    let w = read_be32(d, 0);
    let h = read_be32(d, 4);
    let (bd, ct, comp, filt, il) = (d[8], d[9], d[10], d[11], d[12]);
    let r = [
        w == 0,
        w > 0x7fff_ffff,
        w > wmax,
        h == 0,
        h > 0x7fff_ffff,
        h > hmax,
        !(bd == 1 || bd == 2 || bd == 4 || bd == 8 || bd == 16),
        !(ct == 0 || ct == 2 || ct == 3 || ct == 4 || ct == 6),
        (ct == 3 && bd > 8) || ((ct == 2 || ct == 4 || ct == 6) && bd < 8),
        il >= 2,
        comp != 0,
        filt != 0,
    ];
    proof {
        if forall|j: int| 0 <= j < 12 ==> !#[trigger] r@[j] {
            assert(!r@[0] && !r@[1] && !r@[2] && !r@[3] && !r@[4] && !r@[5]);
            assert(!r@[6] && !r@[7] && !r@[8] && !r@[9] && !r@[10] && !r@[11]);
        }
    }
    r
}

// ---------------------------------------------------------------------------
// PLTE (`png_handle_PLTE`, `png_set_PLTE`)
// ---------------------------------------------------------------------------

/// What the libpng API has accepted so far: libpng's `PNG_HAVE_PLTE` and
/// `PNG_HAVE_IDAT` mode bits, and whether a tRNS and a bKGD chunk have been
/// accepted (`png_has_chunk`); `num_palette`, the entries of the accepted
/// palette.
#[derive(Clone, Copy)]
pub struct Seen {
    pub plte: bool,
    pub idat: bool,
    pub trns: bool,
    pub bkgd: bool,
    pub num_palette: u16,
}

impl Seen {
    /// This is what the specification's walk has recorded, before the
    /// image data, in an image with header `h`.
    pub open spec fn matches(self, h: Ihdr, st: Walk) -> bool {
        &&& !self.idat && st.phase == 0
        &&& self.plte == st.plte is Some
        &&& self.trns == st.trns is Some
        &&& self.bkgd == st.bkgd
        &&& self.num_palette <= 256
        &&& h.ct == 3 && st.plte is Some ==> self.num_palette as nat * 3 == st.plte.unwrap().len()
    }
}

/// The message for a PLTE that is not used.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum PlteMsg {
    Duplicate,
    OutOfPlace,
    Grayscale,
    Invalid,
}

/// What to do with a PLTE chunk.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Plte {
    /// Not used: check the CRC (`crc_as_anc`), then report `msg` as an
    /// error (`fatal`, a palette image) or a benign error.
    Bad { msg: PlteMsg, fatal: bool, crc_as_anc: bool },
    /// Used: check the CRC (`crc_as_anc`; libpng uses the palette whatever
    /// the result unless it is an error), take the first `num` entries;
    /// none is an error ("Invalid palette"). It goes to the decoder when
    /// `forward` (a palette image).
    Good { num: u32, crc_as_anc: bool, forward: bool },
}

/// libpng's decision on a PLTE chunk of length `len` in an image of colour
/// type `ct` and bit depth `depth`: a palette image's palette is cut to
/// the entries its bit depth can index (CVE-2015-8126).
pub open spec fn plte_rule(seen: Seen, ct: u8, depth: u8, len: u32) -> Plte {
    let msg = if seen.plte {
        Some(PlteMsg::Duplicate)
    } else if seen.idat {
        Some(PlteMsg::OutOfPlace)
    } else if ct & 2 == 0 {
        Some(PlteMsg::Grayscale)
    } else if len > 768 || len % 3 != 0 {
        Some(PlteMsg::Invalid)
    } else if ct != 3 && (seen.trns || seen.bkgd) {
        Some(PlteMsg::OutOfPlace)
    } else {
        None
    };
    match msg {
        Some(m) => Plte::Bad { msg: m, fatal: ct == 3, crc_as_anc: ct != 3 },
        None => Plte::Good {
            num: if ct == 3 && depth <= 8 && len / 3 > pow2_nat(depth as nat) {
                pow2_nat(depth as nat) as u32
            } else {
                len / 3
            },
            crc_as_anc: ct != 3,
            forward: ct == 3,
        },
    }
}

/// `plte_rule`.
pub fn plte_check(seen: Seen, ct: u8, depth: u8, len: u32) -> (r: Plte)
    ensures
        r == plte_rule(seen, ct, depth, len),
        match r {
            Plte::Bad { fatal, crc_as_anc, .. } => fatal == (ct == 3) && crc_as_anc == (ct != 3),
            Plte::Good { num, crc_as_anc, forward } => {
                &&& crc_as_anc == (ct != 3) && forward == (ct == 3)
                &&& 3 * num <= len <= 768 && len % 3 == 0
                &&& num as nat == if ct == 3 && depth <= 8 && len / 3 > pow2_nat(depth as nat) {
                    pow2_nat(depth as nat)
                } else {
                    (len / 3) as nat
                }
            },
        },
{
    let msg = if seen.plte {
        Some(PlteMsg::Duplicate)
    } else if seen.idat {
        Some(PlteMsg::OutOfPlace)
    } else if ct & 2 == 0 {
        Some(PlteMsg::Grayscale)
    } else if len > 768 || len % 3 != 0 {
        Some(PlteMsg::Invalid)
    } else if ct != 3 && (seen.trns || seen.bkgd) {
        Some(PlteMsg::OutOfPlace)
    } else {
        None
    };
    match msg {
        Some(m) => Plte::Bad { msg: m, fatal: ct == 3, crc_as_anc: ct != 3 },
        None => {
            proof {
                assert(ct & 2 != 0 ==> ct != 3 || ct == 3);
                reveal_with_fuel(pow2_nat, 9);
            }
            let max: u32 = if ct == 3 && depth < 8 {
                1u32 << (depth as u32)
            } else {
                256
            };
            proof {
                if ct == 3 && depth <= 8 {
                    lemma_pow2_shift(depth);
                }
            }
            let num = if len / 3 > max {
                max
            } else {
                len / 3
            };
            Plte::Good { num, crc_as_anc: ct != 3, forward: ct == 3 }
        },
    }
}

/// `1 << depth` for the depths a palette can have, and for the ones it
/// cannot (up to 8, where `png_check_IHDR` has already failed).
proof fn lemma_pow2_shift(depth: u8)
    requires
        depth <= 8,
    ensures
        depth < 8 ==> (1u32 << (depth as u32)) as nat == pow2_nat(depth as nat),
        depth == 8 ==> pow2_nat(depth as nat) == 256,
{
    reveal_with_fuel(pow2_nat, 9);
    if depth == 0 {
        assert(1u32 << 0u32 == 1) by (bit_vector);
    } else if depth == 1 {
        assert(1u32 << 1u32 == 2) by (bit_vector);
    } else if depth == 2 {
        assert(1u32 << 2u32 == 4) by (bit_vector);
    } else if depth == 3 {
        assert(1u32 << 3u32 == 8) by (bit_vector);
    } else if depth == 4 {
        assert(1u32 << 4u32 == 16) by (bit_vector);
    } else if depth == 5 {
        assert(1u32 << 5u32 == 32) by (bit_vector);
    } else if depth == 6 {
        assert(1u32 << 6u32 == 64) by (bit_vector);
    } else if depth == 7 {
        assert(1u32 << 7u32 == 128) by (bit_vector);
    }
}

/// What becomes of a chunk, all checks made.
pub enum Outcome {
    /// An error: the file is rejected.
    Error,
    /// Ignored (a warning or benign error at most).
    Ignore,
    /// Used, with this many palette entries (PLTE) or as is (tRNS: 0).
    Use(nat),
}

/// PLTE's outcome: `plte_check`, then the CRC check it asks for, then
/// `png_set_PLTE`'s check of an empty palette. Benign errors are warnings
/// (libpng's default for reading).
pub open spec fn plte_outcome(r: Plte, flags: u32, crc_ok: bool, crc: CrcVerdict) -> Outcome {
    match r {
        Plte::Bad { fatal, .. } => if fatal || crc == CrcVerdict::Fail {
            Outcome::Error
        } else {
            Outcome::Ignore
        },
        Plte::Good { num, .. } => if crc == CrcVerdict::Fail || num == 0 {
            Outcome::Error
        } else {
            Outcome::Use(num as nat)
        },
    }
}

/// With libpng's default CRC handling, the PLTE decision before the image
/// data agrees with the specification: the file is rejected at the chunk
/// exactly when `spec::step` rejects it, and a palette image's palette is
/// used exactly when the specification takes it, with as many entries.
pub proof fn theorem_plte(b: Seq<u8>, h: Ihdr, p: int, c: Chunk, st: Walk, seen: Seen, r: Plte, crc: CrcVerdict)
    requires
        c.ty == PLTE,
        depth_ok(h.ct, h.depth),
        h.ct < 256 && h.depth < 256,
        seen.matches(h, st),
        0 <= p && p + 12 + c.len <= b.len(),
        c.len <= MAX_LEN,
        // The decisions made for this chunk.
        r == plte_rule(seen, h.ct as u8, h.depth as u8, c.len as u32),
        // The CRC check `r` asks for (`plte_check` ensures it is as an
        // ancillary chunk's exactly when the image has no palette).
        crc == crc_rule(0, true, h.ct != 3, c.crc_ok),
    ensures
        ({
            let o = plte_outcome(r, 0, c.crc_ok, crc);
            let d = chunk_data(b, p, c.len);
            match step(b, h, p, c, st) {
                Err(x) => !x && o is Error,
                Ok(st2) => {
                    &&& !(o is Error)
                    &&& (h.ct == 3 ==> (o is Use <==> st2.plte != st.plte))
                    &&& (h.ct == 3 ==> match o {
                        Outcome::Use(num) => st2.plte == Some(take_plte(h, d)) && 3 * num == take_plte(h, d).len(),
                        _ => true,
                    })
                    &&& (h.ct != 3 ==> (o is Use <==> st2.plte != st.plte))
                    &&& st2.trns == st.trns && st2.bkgd == st.bkgd && st2.phase == st.phase
                },
            }
        }),
{
    reveal_with_fuel(pow2_nat, 9);
    let d = chunk_data(b, p, c.len);
    assert(d.len() == c.len);
    lemma_flags0(true, h.ct != 3, c.crc_ok);
    assert(is_critical(PLTE)) by (compute_only);
    assert((h.ct as u8) & 2 == 0 <==> (h.ct == 0 || h.ct == 4)) by {
        let ct = h.ct as u8;
        assert(ct == 0 || ct == 2 || ct == 3 || ct == 4 || ct == 6);
        assert((ct == 0 || ct == 2 || ct == 3 || ct == 4 || ct == 6) ==> (ct & 2 == 0 <==> (ct == 0
            || ct == 4))) by (bit_vector);
    }
    if h.ct == 3 {
        if c.len / 3 > pow2_nat(h.depth) {
            assert(take_plte(h, d).len() == 3 * pow2_nat(h.depth));
        }
    }
}

// ---------------------------------------------------------------------------
// tRNS (`png_handle_chunk`'s checks for tRNS, `png_handle_tRNS`)
// ---------------------------------------------------------------------------

/// The benign error for a tRNS chunk that is not used.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum TrnsMsg {
    /// After the image data, or before PLTE in a palette image.
    OutOfPlace,
    Duplicate,
    TooLong,
    Invalid,
    /// In an image with an alpha channel.
    AlphaChannel,
}

/// libpng's decision on a tRNS chunk of length `len` in an image of colour
/// type `ct`: `None` to use it (once its CRC passes), or the benign error
/// that makes it ignored. It is never an error.
pub open spec fn trns_rule(seen: Seen, ct: u8, len: u32) -> Option<TrnsMsg> {
    if seen.idat {
        Some(TrnsMsg::OutOfPlace)
    } else if seen.trns {
        Some(TrnsMsg::Duplicate)
    } else if len > 256 {
        Some(TrnsMsg::TooLong)
    } else if ct == 0 {
        if len != 2 { Some(TrnsMsg::Invalid) } else { None }
    } else if ct == 2 {
        if len != 6 { Some(TrnsMsg::Invalid) } else { None }
    } else if ct == 3 {
        if !seen.plte {
            Some(TrnsMsg::OutOfPlace)
        } else if len > seen.num_palette as u32 || len == 0 {
            Some(TrnsMsg::Invalid)
        } else {
            None
        }
    } else {
        // 4 and 6 (and no other: IHDR has been checked).
        Some(TrnsMsg::AlphaChannel)
    }
}

/// `trns_rule`.
pub fn trns_check(seen: Seen, ct: u8, len: u32) -> (r: Option<TrnsMsg>)
    ensures
        r == trns_rule(seen, ct, len),
        r is None ==> len <= 256 && (ct == 0 ==> len == 2) && (ct == 2 ==> len == 6) && (ct == 3
            ==> 1 <= len <= seen.num_palette) && (ct == 0 || ct == 2 || ct == 3),
{
    if seen.idat {
        Some(TrnsMsg::OutOfPlace)
    } else if seen.trns {
        Some(TrnsMsg::Duplicate)
    } else if len > 256 {
        Some(TrnsMsg::TooLong)
    } else if ct == 0 {
        if len != 2 { Some(TrnsMsg::Invalid) } else { None }
    } else if ct == 2 {
        if len != 6 { Some(TrnsMsg::Invalid) } else { None }
    } else if ct == 3 {
        if !seen.plte {
            Some(TrnsMsg::OutOfPlace)
        } else if len > seen.num_palette as u32 || len == 0 {
            Some(TrnsMsg::Invalid)
        } else {
            None
        }
    } else {
        // 4 and 6 (and no other: IHDR has been checked).
        Some(TrnsMsg::AlphaChannel)
    }
}

/// With libpng's default CRC handling, the tRNS decision before the image
/// data agrees with the specification: the chunk is used (and given to the
/// decoder) exactly when `spec::step` takes it, and is never an error.
pub proof fn theorem_trns(b: Seq<u8>, h: Ihdr, p: int, c: Chunk, st: Walk, seen: Seen, r: Option<TrnsMsg>, crc: CrcVerdict)
    requires
        c.ty == TRNS,
        depth_ok(h.ct, h.depth),
        h.ct < 256,
        seen.matches(h, st),
        0 <= p && p + 12 + c.len <= b.len(),
        c.len <= MAX_LEN,
        r == trns_rule(seen, h.ct as u8, c.len as u32),
        crc == crc_rule(0, false, false, c.crc_ok),
    ensures
        step(b, h, p, c, st) matches Ok(st2) && (st2.trns != st.trns <==> (r is None && crc
            == CrcVerdict::Pass)) && (st2.trns != st.trns ==> st2.trns == Some(chunk_data(b, p, c.len)))
            && st2.plte == st.plte && st2.phase == st.phase,
{
    assert(!is_critical(TRNS)) by (compute_only);
    lemma_flags0(false, false, c.crc_ok);
    assert(chunk_data(b, p, c.len).len() == c.len);
}

/// With libpng's default CRC handling, the CRC check of a critical chunk
/// before the image data (IHDR, PLTE in a palette image, IDAT, an unknown
/// critical chunk) fails exactly when the specification rejects the file
/// for the CRC.
pub proof fn theorem_crc(critical: bool, as_anc: bool, crc_ok: bool)
    requires
        critical,
        !as_anc,
    ensures
        crc_rule(0, critical, as_anc, crc_ok) == if crc_ok {
            CrcVerdict::Pass
        } else {
            CrcVerdict::Fail
        },
{
    lemma_flags0(critical, as_anc, crc_ok);
}

} // verus!
