//! Executable-independent specification of the WHATWG URL Standard
//! (<https://url.spec.whatwg.org/>): the URL record, the host parser, the basic
//! URL parser's state machine and the URL serializer.
//!
//! Each definition transliterates the Standard's algorithm of the same name;
//! the exec parser in `parse.rs` is proven to compute exactly these
//! functions. This file is the trusted specification: read it side by side
//! with the Standard.
//!
//! # Bytes instead of code points
//!
//! The Standard runs on a string of Unicode scalar values. This spec runs on
//! its UTF-8 encoding, one byte per step. The two are equivalent because
//! every decision the parser makes compares the current code point with
//! ASCII characters, and every non-ASCII code point is either
//! - appended verbatim to a buffer (authority, host, port and file host
//!   states), which appends the same scalar value either way;
//! - or UTF-8 percent-encoded, and every percent-encode set contains all
//!   non-ASCII code points, so encoding a code point equals encoding each of
//!   its UTF-8 bytes on its own.
//! Lengths only matter when the authority state rewinds the pointer by the
//! buffer's length, which is the buffer's byte length in this model, and in
//! "starts with a Windows drive letter", whose length test only concerns the
//! first two (ASCII) code points.
//!
//! # What is not modelled
//!
//! - Validation errors (they never change the result).
//! - Encodings other than UTF-8 (a legacy HTML concept; the query is always
//!   encoded as UTF-8 here, as for every non-HTML caller).
//! - Blob URL entries.
//! - UTS #46 processing of non-ASCII domains is vtext's specification of
//!   UTS #46 (`verilith_text::idna::spec`, a transliteration of UTS #46 sections 4
//!   to 4.2 that vtext's own trusted base covers). ASCII domains, which
//!   never reach UTS #46 in the Standard (it lowercases them instead), are
//!   fully specified here.
#[cfg(verus_only)]
pub use verilith_core::num::{decimal, is_digit as is_ascii_digit};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Characters
// ---------------------------------------------------------------------------

pub open spec fn is_ascii_upper_alpha(c: u8) -> bool {
    b'A' <= c <= b'Z'
}

pub open spec fn is_ascii_lower_alpha(c: u8) -> bool {
    b'a' <= c <= b'z'
}

pub open spec fn is_ascii_alpha(c: u8) -> bool {
    is_ascii_upper_alpha(c) || is_ascii_lower_alpha(c)
}

pub open spec fn is_ascii_alphanumeric(c: u8) -> bool {
    is_ascii_digit(c) || is_ascii_alpha(c)
}

pub open spec fn is_ascii_hex_digit(c: u8) -> bool {
    is_ascii_digit(c) || (b'A' <= c <= b'F') || (b'a' <= c <= b'f')
}

pub open spec fn hex_value(c: u8) -> nat {
    if is_ascii_digit(c) {
        (c - b'0') as nat
    } else if b'A' <= c <= b'F' {
        (c - b'A' + 10) as nat
    } else {
        (c - b'a' + 10) as nat
    }
}

pub open spec fn ascii_lowercase(c: u8) -> u8 {
    if is_ascii_upper_alpha(c) {
        (c + 32) as u8
    } else {
        c
    }
}

pub open spec fn ascii_lowercase_seq(s: Seq<u8>) -> Seq<u8> {
    s.map_values(|c: u8| ascii_lowercase(c))
}

/// C0 control or space (stripped from both ends of the input).
pub open spec fn is_c0_control_or_space(c: u8) -> bool {
    c <= 0x20
}

/// ASCII tab or newline (removed from the input).
pub open spec fn is_ascii_tab_or_newline(c: u8) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0D
}

pub open spec fn is_ascii(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] < 0x80
}

// ---------------------------------------------------------------------------
// Percent-encoding (§1.3)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum EncodeSet {
    C0Control,
    Fragment,
    Query,
    SpecialQuery,
    Path,
    Userinfo,
}

pub open spec fn in_c0_control_set(c: u8) -> bool {
    c < 0x20 || c > 0x7E
}

pub open spec fn in_fragment_set(c: u8) -> bool {
    in_c0_control_set(c) || c == b' ' || c == b'"' || c == b'<' || c == b'>' || c == b'`'
}

pub open spec fn in_query_set(c: u8) -> bool {
    in_c0_control_set(c) || c == b' ' || c == b'"' || c == b'#' || c == b'<' || c == b'>'
}

pub open spec fn in_special_query_set(c: u8) -> bool {
    in_query_set(c) || c == b'\''
}

pub open spec fn in_path_set(c: u8) -> bool {
    in_query_set(c) || c == b'?' || c == b'^' || c == b'`' || c == b'{' || c == b'}'
}

pub open spec fn in_userinfo_set(c: u8) -> bool {
    in_path_set(c) || c == b'/' || c == b':' || c == b';' || c == b'=' || c == b'@' || (b'['
        <= c <= b']') || c == b'|'
}

pub open spec fn in_encode_set(set: EncodeSet, c: u8) -> bool {
    match set {
        EncodeSet::C0Control => in_c0_control_set(c),
        EncodeSet::Fragment => in_fragment_set(c),
        EncodeSet::Query => in_query_set(c),
        EncodeSet::SpecialQuery => in_special_query_set(c),
        EncodeSet::Path => in_path_set(c),
        EncodeSet::Userinfo => in_userinfo_set(c),
    }
}

pub open spec fn upper_hex_digit(n: nat) -> u8 {
    if n < 10 {
        (b'0' + n) as u8
    } else {
        (b'A' + n - 10) as u8
    }
}

/// Percent-encode a byte: "%" followed by two ASCII upper hex digits.
pub open spec fn percent_encode_byte(c: u8) -> Seq<u8> {
    seq![b'%', upper_hex_digit((c / 16) as nat), upper_hex_digit((c % 16) as nat)]
}

/// UTF-8 percent-encode one byte of a code point's UTF-8 encoding.
pub open spec fn pe(c: u8, set: EncodeSet) -> Seq<u8> {
    if in_encode_set(set, c) {
        percent_encode_byte(c)
    } else {
        seq![c]
    }
}

/// UTF-8 percent-encode a string (percent-encode after encoding, UTF-8).
pub open spec fn pe_seq(s: Seq<u8>, set: EncodeSet) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        pe_seq(s.drop_last(), set) + pe(s.last(), set)
    }
}

/// Percent-decode a byte sequence.
pub open spec fn percent_decode(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == b'%' && s.len() >= 3 && is_ascii_hex_digit(s[1]) && is_ascii_hex_digit(
        s[2],
    ) {
        seq![(hex_value(s[1]) * 16 + hex_value(s[2])) as u8] + percent_decode(s.skip(3))
    } else {
        seq![s[0]] + percent_decode(s.skip(1))
    }
}

// ---------------------------------------------------------------------------
// Hosts (§3)
// ---------------------------------------------------------------------------

pub enum Host {
    /// A non-empty ASCII string.
    Domain(Seq<u8>),
    Ipv4(u32),
    /// Eight 16-bit pieces.
    Ipv6(Seq<u16>),
    /// A non-empty ASCII string.
    Opaque(Seq<u8>),
    Empty,
}

pub open spec fn is_forbidden_host_code_point(c: u8) -> bool {
    c == 0x00 || c == 0x09 || c == 0x0A || c == 0x0D || c == b' ' || c == b'#' || c == b'/' || c
        == b':' || c == b'<' || c == b'>' || c == b'?' || c == b'@' || c == b'[' || c == b'\\'
        || c == b']' || c == b'^' || c == b'|'
}

pub open spec fn is_forbidden_domain_code_point(c: u8) -> bool {
    is_forbidden_host_code_point(c) || c <= 0x1F || c == b'%' || c == 0x7F
}

pub open spec fn contains_forbidden_host_code_point(s: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_forbidden_host_code_point(#[trigger] s[i])
}

pub open spec fn contains_forbidden_domain_code_point(s: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_forbidden_domain_code_point(#[trigger] s[i])
}

/// Unicode ToASCII (UTS #46) with the parameters of the Standard's "domain
/// parser ToASCII" (beStrict = false), applied to the UTF-8 decoding
/// (without BOM; invalid sequences become U+FFFD) of the given bytes. `None`
/// is failure. Only ever applied to non-ASCII input.
///
/// A ghost step counter for the linear-time proof, erased at run time.
/// Every loop iteration whose count is not bounded by a constant, and every
/// byte copied in bulk, adds one.
pub tracked struct Meter {
    pub ghost n: nat,
}

/// The length of the maximal subpart (Unicode 3.9, D93b) of the ill-formed
/// UTF-8 at `s[i]`: the longest prefix of a well-formed sequence that it
/// starts with, and at least one byte. The Encoding Standard's UTF-8
/// decoder replaces each maximal subpart with one U+FFFD.
pub open spec fn utf8_subpart(s: Seq<u8>, i: int) -> int {
    let b = s[i];
    if 0xE0 <= b <= 0xEF {
        let lo: u8 = if b == 0xE0 { 0xA0 } else { 0x80 };
        let hi: u8 = if b == 0xED { 0x9F } else { 0xBF };
        if verilith_core::utf8::byte_in(s, i + 1, lo, hi) { 2 } else { 1 }
    } else if 0xF0 <= b <= 0xF4 {
        let lo: u8 = if b == 0xF0 { 0x90 } else { 0x80 };
        let hi: u8 = if b == 0xF4 { 0x8F } else { 0xBF };
        if verilith_core::utf8::byte_in(s, i + 1, lo, hi) {
            if verilith_core::utf8::byte_in(s, i + 2, 0x80, 0xBF) { 3 } else { 2 }
        } else {
            1
        }
    } else {
        1
    }
}

/// "UTF-8 decode without BOM" (Encoding Standard) of `s[i..]`: each
/// well-formed sequence (vcore's `utf8_len` gives its length, Table 3-7,
/// and vtext's `dec8_at` its value, Table 3-6) becomes its scalar, and each
/// maximal subpart of ill-formed UTF-8 becomes U+FFFD. The URL Standard
/// strips no BOM here.
pub open spec fn utf8_decode(s: Seq<u8>, i: int) -> Seq<u32>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        Seq::empty()
    } else {
        match verilith_core::utf8::utf8_len(s, i) {
            Some(l) => if l > 0 {
                seq![verilith_text::utf::spec::dec8_at(s, i, l)] + utf8_decode(s, i + l)
            } else {
                Seq::empty()
            },
            None => seq![0xFFFDu32] + utf8_decode(s, i + utf8_subpart(s, i)),
        }
    }
}

/// The URL Standard's flags for UTS #46 without beStrict (vtext's
/// `Options::URL`): CheckHyphens false, CheckBidi true, CheckJoiners true,
/// UseSTD3ASCIIRules false, Transitional_Processing false,
/// VerifyDnsLength false.
pub open spec fn url_options() -> verilith_text::idna::spec::Options {
    verilith_text::idna::spec::Options {
        check_hyphens: false,
        check_bidi: true,
        check_joiners: true,
        use_std3_ascii_rules: false,
        transitional: false,
        verify_dns_length: false,
    }
}

/// vtext's UTS #46 ToASCII with the URL Standard's flags (it lowercases an
/// ASCII domain instead, which `domain_parse_result` does itself).
pub open spec fn url_domain_to_ascii_url(cs: Seq<u32>) -> Option<Seq<u8>> {
    verilith_text::idna::uts46::url_domain_to_ascii(cs, url_options())
}

/// "Let asciiDomain be the result of running domain to ASCII with domain"
/// on "the result of running UTF-8 decode without BOM on the
/// percent-decoding of input": the decoding, with U+FFFD for ill-formed
/// UTF-8, goes to UTS #46 as it is. A result more than 8 bytes per input
/// byte also fails: a limit the Standard does not have, which keeps the
/// parser's output linear. No domain is known to reach it; over every code
/// point the largest ratio is 5.67 (U+337F). (Opaque: the parser's proofs
/// treat it as a black box, and only `idna.rs` looks inside.)
#[verifier::opaque]
pub open spec fn domain_to_ascii(domain: Seq<u8>) -> Option<Seq<u8>> {
    match url_domain_to_ascii_url(utf8_decode(domain, 0)) {
        Some(v) if v.len() <= 8 * domain.len() => Some(v),
        _ => None,
    }
}

/// Strictly split `s` on `d`.
pub open spec fn split(s: Seq<u8>, d: u8) -> Seq<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![Seq::empty()]
    } else {
        let rest = split(s.skip(1), d);
        if s[0] == d {
            seq![Seq::empty()] + rest
        } else {
            rest.update(0, seq![s[0]] + rest[0])
        }
    }
}

pub open spec fn is_radix_digit(c: u8, r: nat) -> bool {
    if r == 16 {
        is_ascii_hex_digit(c)
    } else if r == 10 {
        is_ascii_digit(c)
    } else {
        b'0' <= c <= b'7'
    }
}

/// The value of `s` in radix `r` (digits assumed valid).
pub open spec fn radix_value(s: Seq<u8>, r: nat) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        radix_value(s.drop_last(), r) * r + hex_value(s.last())
    }
}

/// The IPv4 number parser's radix R for input `s`.
pub open spec fn ipv4_radix(s: Seq<u8>) -> nat {
    if s.len() >= 2 && s[0] == b'0' && (s[1] == b'x' || s[1] == b'X') {
        16
    } else if s.len() >= 2 && s[0] == b'0' {
        8
    } else {
        10
    }
}

/// The IPv4 number parser's input after removing the "0x" or "0" prefix.
pub open spec fn ipv4_digits(s: Seq<u8>) -> Seq<u8> {
    if ipv4_radix(s) == 16 {
        s.skip(2)
    } else if ipv4_radix(s) == 8 {
        s.skip(1)
    } else {
        s
    }
}

/// The IPv4 number parser: the number and whether it was not decimal.
pub open spec fn ipv4_number(s: Seq<u8>) -> Option<(nat, bool)> {
    let r = ipv4_radix(s);
    let t = ipv4_digits(s);
    if s.len() == 0 {
        None
    } else if t.len() == 0 {
        Some((0, true))
    } else if exists|i: int| 0 <= i < t.len() && !is_radix_digit(#[trigger] t[i], r) {
        None
    } else {
        Some((radix_value(t, r), r != 10))
    }
}

pub open spec fn all_ascii_digits(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_ascii_digit(#[trigger] s[i])
}

/// Some item but the last exceeds 255.
pub open spec fn some_non_last_over_255(numbers: Seq<nat>) -> bool {
    exists|i: int| 0 <= i < numbers.len() - 1 && #[trigger] numbers[i] > 255
}

/// The ends in a number checker.
pub open spec fn ends_in_a_number(s: Seq<u8>) -> bool {
    let parts0 = split(s, b'.');
    let parts = if parts0.last().len() == 0 {
        parts0.drop_last()
    } else {
        parts0
    };
    if parts.len() == 0 {
        false
    } else {
        let last = parts.last();
        if last.len() > 0 && all_ascii_digits(last) {
            true
        } else {
            ipv4_number(last) is Some
        }
    }
}

/// Parses every part with the IPv4 number parser.
pub open spec fn ipv4_numbers(parts: Seq<Seq<u8>>) -> Option<Seq<nat>>
    decreases parts.len(),
{
    if parts.len() == 0 {
        Some(Seq::empty())
    } else {
        match ipv4_number(parts[0]) {
            None => None,
            Some((n, _)) => match ipv4_numbers(parts.skip(1)) {
                None => None,
                Some(ns) => Some(seq![n] + ns),
            },
        }
    }
}

pub open spec fn pow256(e: nat) -> nat
    decreases e,
{
    if e == 0 {
        1
    } else {
        256 * pow256((e - 1) as nat)
    }
}

/// Sum of `numbers[i] * 256^(3 - i)` for `i < numbers.len()`.
pub open spec fn ipv4_prefix_sum(numbers: Seq<nat>) -> nat
    decreases numbers.len(),
{
    if numbers.len() == 0 {
        0
    } else {
        ipv4_prefix_sum(numbers.drop_last()) + numbers.last() * pow256(
            (3 - (numbers.len() - 1)) as nat,
        )
    }
}

/// The IPv4 parser.
pub open spec fn ipv4_parse(s: Seq<u8>) -> Option<u32> {
    let parts0 = split(s, b'.');
    let parts = if parts0.last().len() == 0 && parts0.len() > 1 {
        parts0.drop_last()
    } else {
        parts0
    };
    ipv4_parse_parts(parts)
}

/// The IPv4 parser, from "If parts's size is greater than 4" on.
pub open spec fn ipv4_parse_parts(parts: Seq<Seq<u8>>) -> Option<u32> {
    if parts.len() > 4 {
        None
    } else {
        match ipv4_numbers(parts) {
            None => None,
            Some(numbers) => ipv4_from_numbers(numbers),
        }
    }
}

/// The IPv4 parser, from "If any item in numbers is greater than 255" on.
pub open spec fn ipv4_from_numbers(numbers: Seq<nat>) -> Option<u32> {
    if some_non_last_over_255(numbers) {
        None
    } else if numbers.last() >= pow256((5 - numbers.len()) as nat) {
        None
    } else {
        Some((numbers.last() + ipv4_prefix_sum(numbers.drop_last())) as u32)
    }
}

/// Up to four ASCII hex digits at `p`: their value and count.
pub open spec fn ipv6_hex_run(s: Seq<u8>, p: int, value: nat, length: nat) -> (nat, nat)
    decreases 4 - length,
{
    if length < 4 && 0 <= p + length < s.len() && is_ascii_hex_digit(s[p + length]) {
        ipv6_hex_run(s, p, value * 16 + hex_value(s[p + length]), length + 1)
    } else {
        (value, length)
    }
}

/// The inner "while c is an ASCII digit" loop of an IPv4 piece. Returns the
/// piece and the pointer after it.
pub open spec fn ipv6_v4_digits(s: Seq<u8>, p: int, piece: Option<nat>) -> Option<(nat, int)>
    decreases s.len() - p,
{
    if 0 <= p < s.len() && is_ascii_digit(s[p]) {
        let number = hex_value(s[p]);
        match piece {
            None => ipv6_v4_digits(s, p + 1, Some(number)),
            Some(v) => if v == 0 {
                None
            } else if v * 10 + number > 255 {
                None
            } else {
                ipv6_v4_digits(s, p + 1, Some(v * 10 + number))
            },
        }
    } else {
        match piece {
            None => None,
            Some(v) => Some((v, p)),
        }
    }
}

/// The IPv4-in-IPv6 loop. Returns the address and piece index.
pub open spec fn ipv6_v4(
    s: Seq<u8>,
    p: int,
    numbers_seen: nat,
    piece_index: int,
    address: Seq<nat>,
) -> Option<(Seq<nat>, int)>
    decreases s.len() - p via ipv6_v4_decreases
{
    if p < 0 || p >= s.len() {
        if numbers_seen != 4 {
            None
        } else {
            Some((address, piece_index))
        }
    } else {
        let p1 = if numbers_seen > 0 {
            if s[p] == b'.' && numbers_seen < 4 {
                p + 1
            } else {
                -1
            }
        } else {
            p
        };
        if p1 < 0 {
            None
        } else {
            match ipv6_v4_digits(s, p1, None) {
                None => None,
                Some((piece, p2)) => {
                    let address2 = address.update(piece_index, address[piece_index] * 0x100 + piece);
                    let ns = numbers_seen + 1;
                    let pi = if ns == 2 || ns == 4 {
                        piece_index + 1
                    } else {
                        piece_index
                    };
                    ipv6_v4(s, p2, ns, pi, address2)
                },
            }
        }
    }
}

proof fn lemma_ipv6_v4_digits(s: Seq<u8>, p: int, piece: Option<nat>)
    requires
        0 <= p <= s.len(),
    ensures
        ipv6_v4_digits(s, p, piece) matches Some((_, q)) ==> p <= q <= s.len() && (piece is None
            ==> p < q),
    decreases s.len() - p,
{
    if p < s.len() && is_ascii_digit(s[p]) {
        let number = hex_value(s[p]);
        match piece {
            None => lemma_ipv6_v4_digits(s, p + 1, Some(number)),
            Some(v) => lemma_ipv6_v4_digits(s, p + 1, Some(v * 10 + number)),
        }
    }
}

#[verifier::decreases_by]
proof fn ipv6_v4_decreases(
    s: Seq<u8>,
    p: int,
    numbers_seen: nat,
    piece_index: int,
    address: Seq<nat>,
) {
    if 0 <= p < s.len() {
        lemma_ipv6_v4_digits(s, p, None);
        lemma_ipv6_v4_digits(s, p + 1, None);
    }
}

/// The main loop of the IPv6 parser ("while c is not the EOF code point").
/// Returns the address, piece index and compress.
pub open spec fn ipv6_main(
    s: Seq<u8>,
    p: int,
    piece_index: int,
    compress: Option<int>,
    address: Seq<nat>,
) -> Option<(Seq<nat>, int, Option<int>)>
    decreases s.len() - p,
{
    if p < 0 || p >= s.len() {
        Some((address, piece_index, compress))
    } else if piece_index == 8 {
        None
    } else if s[p] == b':' {
        if compress is Some {
            None
        } else {
            ipv6_main(s, p + 1, piece_index + 1, Some(piece_index + 1), address)
        }
    } else {
        let (value, length) = ipv6_hex_run(s, p, 0, 0);
        let q = p + length;
        if q < s.len() && s[q] == b'.' {
            if length == 0 {
                None
            } else if piece_index > 6 {
                None
            } else {
                match ipv6_v4(s, p, 0, piece_index, address) {
                    None => None,
                    Some((a, pi)) => Some((a, pi, compress)),
                }
            }
        } else if q < s.len() && s[q] == b':' {
            if q + 1 >= s.len() {
                None
            } else {
                ipv6_main(s, q + 1, piece_index + 1, compress, address.update(piece_index, value))
            }
        } else if q < s.len() {
            None
        } else {
            Some((address.update(piece_index, value), piece_index + 1, compress))
        }
    }
}

/// "While pieceIndex is not 0 and swaps is greater than 0, swap
/// address[pieceIndex] with address[compress + swaps - 1], and then decrease
/// both pieceIndex and swaps by 1."
pub open spec fn ipv6_swap(address: Seq<nat>, piece_index: int, swaps: int, compress: int) -> Seq<
    nat,
>
    decreases swaps,
{
    if piece_index == 0 || swaps <= 0 {
        address
    } else {
        let j = compress + swaps - 1;
        let a = address.update(piece_index, address[j]).update(j, address[piece_index]);
        ipv6_swap(a, piece_index - 1, swaps - 1, compress)
    }
}

/// The IPv6 parser.
pub open spec fn ipv6_parse(s: Seq<u8>) -> Option<Seq<u16>> {
    let zero = Seq::new(8, |i: int| 0nat);
    let start = if s.len() > 0 && s[0] == b':' {
        if s.len() < 2 || s[1] != b':' {
            None
        } else {
            Some((2int, 1int, Some(1int)))
        }
    } else {
        Some((0int, 0int, None))
    };
    match start {
        None => None,
        Some((p, pi, compress)) => match ipv6_main(s, p, pi, compress, zero) {
            None => None,
            Some((address, piece_index, compress)) => {
                let result = match compress {
                    Some(c) => Some(ipv6_swap(address, 7, piece_index - c, c)),
                    None => if piece_index != 8 {
                        None
                    } else {
                        Some(address)
                    },
                };
                match result {
                    None => None,
                    Some(a) => Some(Seq::new(8, |i: int| a[i] as u16)),
                }
            },
        },
    }
}

/// The opaque-host parser.
pub open spec fn opaque_host_parse(s: Seq<u8>) -> Option<Host> {
    if contains_forbidden_host_code_point(s) {
        None
    } else {
        let e = pe_seq(s, EncodeSet::C0Control);
        if e.len() == 0 {
            Some(Host::Empty)
        } else {
            Some(Host::Opaque(e))
        }
    }
}

/// The domain parser's result for a percent-decoded domain (beStrict false):
/// ASCII domains are lowercased; others go through UTS #46 ToASCII. ToASCII
/// only ever returns ASCII; a non-ASCII result is treated as failure.
pub open spec fn domain_parse(domain: Seq<u8>) -> Option<Seq<u8>> {
    match domain_parse_result(domain) {
        None => None,
        Some(r) => domain_check(r),
    }
}

/// "If domain is an ASCII string, then set result to domain, lowercased.
/// Otherwise, set result to the result of running domain parser ToASCII."
pub open spec fn domain_parse_result(domain: Seq<u8>) -> Option<Seq<u8>> {
    if is_ascii(domain) {
        Some(ascii_lowercase_seq(domain))
    } else {
        match domain_to_ascii(domain) {
            Some(r) => if is_ascii(r) {
                Some(r)
            } else {
                None
            },
            None => None,
        }
    }
}

/// "If result is the empty string, then return failure. If result contains
/// a forbidden domain code point, then return failure. Return result."
pub open spec fn domain_check(r: Seq<u8>) -> Option<Seq<u8>> {
    if r.len() == 0 {
        None
    } else if contains_forbidden_domain_code_point(r) {
        None
    } else {
        Some(r)
    }
}

/// The host parser.
pub open spec fn host_parse(s: Seq<u8>, is_opaque: bool) -> Option<Host> {
    if s.len() > 0 && s[0] == b'[' {
        if s.last() != b']' {
            None
        } else {
            match ipv6_parse(s.subrange(1, s.len() - 1)) {
                None => None,
                Some(a) => Some(Host::Ipv6(a)),
            }
        }
    } else if is_opaque {
        opaque_host_parse(s)
    } else {
        match domain_parse(percent_decode(s)) {
            None => None,
            Some(ascii) => if ends_in_a_number(ascii) {
                match ipv4_parse(ascii) {
                    None => None,
                    Some(a) => Some(Host::Ipv4(a)),
                }
            } else {
                Some(Host::Domain(ascii))
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Host serializing
// ---------------------------------------------------------------------------

pub open spec fn lower_hex_digit(n: nat) -> u8 {
    if n < 10 {
        (b'0' + n) as u8
    } else {
        (b'a' + n - 10) as u8
    }
}

/// The shortest lowercase hexadecimal representation of `n`.
pub open spec fn lower_hex(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 16 {
        seq![lower_hex_digit(n)]
    } else {
        lower_hex(n / 16) + seq![lower_hex_digit(n % 16)]
    }
}

pub open spec fn ipv4_serialize(a: u32) -> Seq<u8> {
    decimal((a / 0x100_0000) as nat) + seq![b'.'] + decimal(((a / 0x1_0000) % 256) as nat) + seq![
        b'.',
    ] + decimal(((a / 0x100) % 256) as nat) + seq![b'.'] + decimal((a % 256) as nat)
}

/// Finding the IPv6 address compressed piece index, from piece `i` on.
pub open spec fn ipv6_compress_from(
    pieces: Seq<u16>,
    i: int,
    longest_index: Option<int>,
    longest_size: int,
    found_index: Option<int>,
    found_size: int,
) -> Option<int>
    decreases 8 - i,
{
    if i >= 8 {
        if found_size > longest_size {
            found_index
        } else {
            longest_index
        }
    } else if pieces[i] != 0 {
        let (li, ls) = if found_size > longest_size {
            (found_index, found_size)
        } else {
            (longest_index, longest_size)
        };
        ipv6_compress_from(pieces, i + 1, li, ls, None, 0)
    } else {
        let fi = if found_index is None {
            Some(i)
        } else {
            found_index
        };
        ipv6_compress_from(pieces, i + 1, longest_index, longest_size, fi, found_size + 1)
    }
}

pub open spec fn ipv6_compress(pieces: Seq<u16>) -> Option<int> {
    ipv6_compress_from(pieces, 0, None, 1, None, 0)
}

/// The IPv6 serializer's loop, from piece `i` on.
pub open spec fn ipv6_serialize_from(pieces: Seq<u16>, i: int, compress: Option<int>, ignore0: bool) -> Seq<
    u8,
>
    decreases 8 - i,
{
    if i >= 8 {
        Seq::empty()
    } else if ignore0 && pieces[i] == 0 {
        ipv6_serialize_from(pieces, i + 1, compress, true)
    } else if compress == Some(i) {
        let sep = if i == 0 {
            seq![b':', b':']
        } else {
            seq![b':']
        };
        sep + ipv6_serialize_from(pieces, i + 1, compress, true)
    } else {
        lower_hex(pieces[i] as nat) + (if i != 7 {
            seq![b':']
        } else {
            Seq::empty()
        }) + ipv6_serialize_from(pieces, i + 1, compress, false)
    }
}

pub open spec fn ipv6_serialize(pieces: Seq<u16>) -> Seq<u8> {
    ipv6_serialize_from(pieces, 0, ipv6_compress(pieces), false)
}

/// The host serializer.
pub open spec fn host_serialize(h: Host) -> Seq<u8> {
    match h {
        Host::Domain(s) => s,
        Host::Ipv4(a) => ipv4_serialize(a),
        Host::Ipv6(a) => seq![b'['] + ipv6_serialize(a) + seq![b']'],
        Host::Opaque(s) => s,
        Host::Empty => Seq::empty(),
    }
}

// ---------------------------------------------------------------------------
// URLs (§4)
// ---------------------------------------------------------------------------

pub enum UrlPath {
    /// An opaque path (a single URL path segment).
    Opaque(Seq<u8>),
    /// A list of URL path segments.
    List(Seq<Seq<u8>>),
}

/// A URL record.
pub struct UrlRecord {
    pub scheme: Seq<u8>,
    pub username: Seq<u8>,
    pub password: Seq<u8>,
    pub host: Option<Host>,
    pub port: Option<u16>,
    pub path: UrlPath,
    pub query: Option<Seq<u8>>,
    pub fragment: Option<Seq<u8>>,
}

pub open spec fn new_url() -> UrlRecord {
    UrlRecord {
        scheme: Seq::empty(),
        username: Seq::empty(),
        password: Seq::empty(),
        host: None,
        port: None,
        path: UrlPath::List(Seq::empty()),
        query: None,
        fragment: None,
    }
}

pub open spec fn s_ftp() -> Seq<u8> {
    seq![b'f', b't', b'p']
}

pub open spec fn s_file() -> Seq<u8> {
    seq![b'f', b'i', b'l', b'e']
}

pub open spec fn s_http() -> Seq<u8> {
    seq![b'h', b't', b't', b'p']
}

pub open spec fn s_https() -> Seq<u8> {
    seq![b'h', b't', b't', b'p', b's']
}

pub open spec fn s_ws() -> Seq<u8> {
    seq![b'w', b's']
}

pub open spec fn s_wss() -> Seq<u8> {
    seq![b'w', b's', b's']
}

pub open spec fn s_localhost() -> Seq<u8> {
    seq![b'l', b'o', b'c', b'a', b'l', b'h', b'o', b's', b't']
}

pub open spec fn is_special_scheme(s: Seq<u8>) -> bool {
    s == s_ftp() || s == s_file() || s == s_http() || s == s_https() || s == s_ws() || s == s_wss()
}

pub open spec fn default_port(s: Seq<u8>) -> Option<u16> {
    if s == s_ftp() {
        Some(21u16)
    } else if s == s_http() || s == s_ws() {
        Some(80u16)
    } else if s == s_https() || s == s_wss() {
        Some(443u16)
    } else {
        None
    }
}

pub open spec fn is_special(url: UrlRecord) -> bool {
    is_special_scheme(url.scheme)
}

pub open spec fn includes_credentials(url: UrlRecord) -> bool {
    url.username.len() > 0 || url.password.len() > 0
}

pub open spec fn is_windows_drive_letter(s: Seq<u8>) -> bool {
    s.len() == 2 && is_ascii_alpha(s[0]) && (s[1] == b':' || s[1] == b'|')
}

pub open spec fn is_normalized_windows_drive_letter(s: Seq<u8>) -> bool {
    s.len() == 2 && is_ascii_alpha(s[0]) && s[1] == b':'
}

pub open spec fn starts_with_windows_drive_letter(s: Seq<u8>) -> bool {
    &&& s.len() >= 2
    &&& is_ascii_alpha(s[0])
    &&& (s[1] == b':' || s[1] == b'|')
    &&& (s.len() == 2 || s[2] == b'/' || s[2] == b'\\' || s[2] == b'?' || s[2] == b'#')
}

pub open spec fn is_single_dot_segment(s: Seq<u8>) -> bool {
    s == seq![b'.'] || ascii_lowercase_seq(s) == seq![b'%', b'2', b'e']
}

pub open spec fn is_double_dot_segment(s: Seq<u8>) -> bool {
    let l = ascii_lowercase_seq(s);
    s == seq![b'.', b'.'] || l == seq![b'.', b'%', b'2', b'e'] || l == seq![b'%', b'2', b'e', b'.']
        || l == seq![b'%', b'2', b'e', b'%', b'2', b'e']
}

/// Shorten a URL's path.
pub open spec fn shorten_path(url: UrlRecord) -> UrlRecord {
    match url.path {
        UrlPath::List(segs) => if url.scheme == s_file() && segs.len() == 1
            && is_normalized_windows_drive_letter(segs[0]) {
            url
        } else if segs.len() > 0 {
            UrlRecord { path: UrlPath::List(segs.drop_last()), ..url }
        } else {
            url
        },
        UrlPath::Opaque(_) => url,
    }
}

/// Append a segment to a URL's (list) path.
pub open spec fn push_segment(url: UrlRecord, seg: Seq<u8>) -> UrlRecord {
    match url.path {
        UrlPath::List(segs) => UrlRecord { path: UrlPath::List(segs.push(seg)), ..url },
        UrlPath::Opaque(_) => url,
    }
}

pub open spec fn path_is_empty_list(url: UrlRecord) -> bool {
    url.path == UrlPath::List(Seq::<Seq<u8>>::empty())
}

// ---------------------------------------------------------------------------
// The basic URL parser (§4.4)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum State {
    SchemeStart,
    Scheme,
    NoScheme,
    SpecialRelativeOrAuthority,
    PathOrAuthority,
    Relative,
    RelativeSlash,
    SpecialAuthoritySlashes,
    SpecialAuthorityIgnoreSlashes,
    Authority,
    Host,
    Hostname,
    Port,
    File,
    FileSlash,
    FileHost,
    PathStart,
    Path,
    OpaquePath,
    Query,
    Fragment,
}

/// The parser's variables, besides the pointer.
pub struct Machine {
    pub state: State,
    pub url: UrlRecord,
    pub buffer: Seq<u8>,
    pub at_sign_seen: bool,
    pub inside_brackets: bool,
    pub password_token_seen: bool,
}

/// The outcome of running one state.
pub enum Step {
    /// Keep going, with the pointer as the state left it (before the
    /// machine's "increase pointer by 1").
    Next(Machine, int),
    /// "Return failure."
    Fail,
    /// "Return" (only with a state override): stop with the URL as it is.
    Return(UrlRecord),
}

/// The authority state's "for each codePoint in buffer" loop, over the
/// buffer's bytes. Returns the username, password and passwordTokenSeen.
pub open spec fn append_userinfo(buf: Seq<u8>, username: Seq<u8>, password: Seq<u8>, pts: bool) -> (
    Seq<u8>,
    Seq<u8>,
    bool,
)
    decreases buf.len(),
{
    if buf.len() == 0 {
        (username, password, pts)
    } else if buf[0] == b':' && !pts {
        append_userinfo(buf.skip(1), username, password, true)
    } else {
        let e = pe(buf[0], EncodeSet::Userinfo);
        if pts {
            append_userinfo(buf.skip(1), username, password + e, pts)
        } else {
            append_userinfo(buf.skip(1), username + e, password, pts)
        }
    }
}

pub open spec fn is_eof(input: Seq<u8>, p: int) -> bool {
    p >= input.len()
}

/// `c` is the code point at `p` and equals `x`.
pub open spec fn c_is(input: Seq<u8>, p: int, x: u8) -> bool {
    0 <= p < input.len() && input[p] == x
}

/// "remaining starts with x".
pub open spec fn remaining_starts_with(input: Seq<u8>, p: int, x: u8) -> bool {
    c_is(input, p + 1, x)
}

/// c is the EOF code point, "/", "?" or "#", or url is special and c is "\".
pub open spec fn is_authority_end(input: Seq<u8>, p: int, special: bool) -> bool {
    is_eof(input, p) || c_is(input, p, b'/') || c_is(input, p, b'?') || c_is(input, p, b'#') || (
    special && c_is(input, p, b'\\'))
}

pub open spec fn step_scheme_start(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if !eof && is_ascii_alpha(c) {
        Step::Next(
            Machine { buffer: m.buffer.push(ascii_lowercase(c)), state: State::Scheme, ..m },
            p,
        )
    } else if !has_override {
        Step::Next(Machine { state: State::NoScheme, ..m }, p - 1)
    } else {
        Step::Fail
    }
}

pub open spec fn step_scheme(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if !eof && (is_ascii_alphanumeric(c) || c == b'+' || c == b'-' || c == b'.') {
        Step::Next(Machine { buffer: m.buffer.push(ascii_lowercase(c)), ..m }, p)
    } else if !eof && c == b':' {
        let buffer = m.buffer;
        if has_override && is_special_scheme(url.scheme) && !is_special_scheme(buffer) {
            Step::Return(url)
        } else if has_override && !is_special_scheme(url.scheme) && is_special_scheme(
            buffer,
        ) {
            Step::Return(url)
        } else if has_override && (includes_credentials(url) || url.port is Some) && buffer
            == s_file() {
            Step::Return(url)
        } else if has_override && url.scheme == s_file() && url.host == Some(Host::Empty) {
            Step::Return(url)
        } else {
            let url = UrlRecord { scheme: buffer, ..url };
            if has_override {
                let url = if url.port == default_port(url.scheme) {
                    UrlRecord { port: None, ..url }
                } else {
                    url
                };
                Step::Return(url)
            } else {
                let m = Machine { url, buffer: Seq::empty(), ..m };
                if url.scheme == s_file() {
                    Step::Next(Machine { state: State::File, ..m }, p)
                } else if is_special(url) && base is Some && base->0.scheme == url.scheme {
                    Step::Next(Machine { state: State::SpecialRelativeOrAuthority, ..m }, p)
                } else if is_special(url) {
                    Step::Next(Machine { state: State::SpecialAuthoritySlashes, ..m }, p)
                } else if remaining_starts_with(input, p, b'/') {
                    Step::Next(Machine { state: State::PathOrAuthority, ..m }, p + 1)
                } else {
                    Step::Next(
                        Machine {
                            state: State::OpaquePath,
                            url: UrlRecord { path: UrlPath::Opaque(Seq::empty()), ..url },
                            ..m
                        },
                        p,
                    )
                }
            }
        }
    } else if !has_override {
        // Start over from the first code point.
        Step::Next(Machine { buffer: Seq::empty(), state: State::NoScheme, ..m }, -1)
    } else {
        Step::Fail
    }
}

pub open spec fn step_no_scheme(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    match base {
        None => Step::Fail,
        Some(b) => {
            let opaque = b.path is Opaque;
            if opaque && c_is(input, p, b'#') {
                Step::Next(
                    Machine {
                        state: State::Fragment,
                        url: UrlRecord {
                            scheme: b.scheme,
                            path: b.path,
                            query: b.query,
                            fragment: Some(Seq::empty()),
                            ..url
                        },
                        ..m
                    },
                    p,
                )
            } else if opaque {
                Step::Fail
            } else if b.scheme != s_file() {
                Step::Next(Machine { state: State::Relative, ..m }, p - 1)
            } else {
                Step::Next(Machine { state: State::File, ..m }, p - 1)
            }
        },
    }
}

pub open spec fn step_special_relative_or_authority(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if c_is(input, p, b'/') && remaining_starts_with(input, p, b'/') {
        Step::Next(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..m }, p + 1)
    } else {
        Step::Next(Machine { state: State::Relative, ..m }, p - 1)
    }
}

pub open spec fn step_path_or_authority(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if c_is(input, p, b'/') {
        Step::Next(Machine { state: State::Authority, ..m }, p)
    } else {
        Step::Next(Machine { state: State::Path, ..m }, p - 1)
    }
}

pub open spec fn step_relative(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    match base {
        None => Step::Fail,  // unreachable: only entered with a base
        Some(b) => {
            let url = UrlRecord { scheme: b.scheme, ..url };
            if c_is(input, p, b'/') || (is_special(url) && c_is(input, p, b'\\')) {
                Step::Next(Machine { state: State::RelativeSlash, url, ..m }, p)
            } else {
                let url = UrlRecord {
                    username: b.username,
                    password: b.password,
                    host: b.host,
                    port: b.port,
                    path: b.path,
                    query: b.query,
                    ..url
                };
                if c_is(input, p, b'?') {
                    Step::Next(
                        Machine {
                            state: State::Query,
                            url: UrlRecord { query: Some(Seq::empty()), ..url },
                            ..m
                        },
                        p,
                    )
                } else if c_is(input, p, b'#') {
                    Step::Next(
                        Machine {
                            state: State::Fragment,
                            url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                            ..m
                        },
                        p,
                    )
                } else if !eof {
                    let url = shorten_path(UrlRecord { query: None, ..url });
                    Step::Next(Machine { state: State::Path, url, ..m }, p - 1)
                } else {
                    Step::Next(Machine { url, ..m }, p)
                }
            }
        },
    }
}

pub open spec fn step_relative_slash(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if special && (c_is(input, p, b'/') || c_is(input, p, b'\\')) {
        Step::Next(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..m }, p)
    } else if c_is(input, p, b'/') {
        Step::Next(Machine { state: State::Authority, ..m }, p)
    } else {
        match base {
            None => Step::Fail,  // unreachable: only entered with a base
            Some(b) => {
                let url = UrlRecord {
                    username: b.username,
                    password: b.password,
                    host: b.host,
                    port: b.port,
                    ..url
                };
                Step::Next(Machine { state: State::Path, url, ..m }, p - 1)
            },
        }
    }
}

pub open spec fn step_special_authority_slashes(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if c_is(input, p, b'/') && remaining_starts_with(input, p, b'/') {
        Step::Next(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..m }, p + 1)
    } else {
        Step::Next(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..m }, p - 1)
    }
}

pub open spec fn step_special_authority_ignore_slashes(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if !c_is(input, p, b'/') && !c_is(input, p, b'\\') {
        Step::Next(Machine { state: State::Authority, ..m }, p - 1)
    } else {
        Step::Next(m, p)
    }
}

pub open spec fn step_authority(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if c_is(input, p, b'@') {
        let buf = if m.at_sign_seen {
            seq![b'%', b'4', b'0'] + m.buffer
        } else {
            m.buffer
        };
        let (username, password, pts) = append_userinfo(
            buf,
            url.username,
            url.password,
            m.password_token_seen,
        );
        Step::Next(
            Machine {
                at_sign_seen: true,
                password_token_seen: pts,
                url: UrlRecord { username, password, ..url },
                buffer: Seq::empty(),
                ..m
            },
            p,
        )
    } else if is_authority_end(input, p, special) {
        if m.at_sign_seen && m.buffer.len() == 0 {
            Step::Fail
        } else {
            Step::Next(
                Machine { buffer: Seq::empty(), state: State::Host, ..m },
                p - m.buffer.len() - 1,
            )
        }
    } else {
        Step::Next(Machine { buffer: m.buffer.push(c), ..m }, p)
    }
}

pub open spec fn step_host(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if has_override && url.scheme == s_file() {
        Step::Next(Machine { state: State::FileHost, ..m }, p - 1)
    } else if c_is(input, p, b':') && !m.inside_brackets {
        if m.buffer.len() == 0 {
            Step::Fail
        } else if state_override == Some(State::Hostname) {
            Step::Fail
        } else {
            match host_parse(m.buffer, !special) {
                None => Step::Fail,
                Some(h) => Step::Next(
                    Machine {
                        url: UrlRecord { host: Some(h), ..url },
                        buffer: Seq::empty(),
                        state: State::Port,
                        ..m
                    },
                    p,
                ),
            }
        }
    } else if is_authority_end(input, p, special) {
        if special && m.buffer.len() == 0 {
            Step::Fail
        } else if has_override && m.buffer.len() == 0 && (includes_credentials(url)
            || url.port is Some) {
            Step::Fail
        } else {
            match host_parse(m.buffer, !special) {
                None => Step::Fail,
                Some(h) => {
                    let url = UrlRecord { host: Some(h), ..url };
                    if has_override {
                        Step::Return(url)
                    } else {
                        Step::Next(
                            Machine {
                                url,
                                buffer: Seq::empty(),
                                state: State::PathStart,
                                ..m
                            },
                            p - 1,
                        )
                    }
                },
            }
        }
    } else {
        let ib = if c == b'[' {
            true
        } else if c == b']' {
            false
        } else {
            m.inside_brackets
        };
        Step::Next(Machine { inside_brackets: ib, buffer: m.buffer.push(c), ..m }, p)
    }
}

pub open spec fn step_port(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if !eof && is_ascii_digit(c) {
        Step::Next(Machine { buffer: m.buffer.push(c), ..m }, p)
    } else if is_authority_end(input, p, special) || has_override {
        if m.buffer.len() > 0 {
            let port = radix_value(m.buffer, 10);
            if port > 65535 {
                Step::Fail
            } else {
                let url = UrlRecord {
                    port: if default_port(url.scheme) == Some(port as u16) {
                        None
                    } else {
                        Some(port as u16)
                    },
                    ..url
                };
                if has_override {
                    Step::Return(url)
                } else {
                    Step::Next(
                        Machine { url, buffer: Seq::empty(), state: State::PathStart, ..m },
                        p - 1,
                    )
                }
            }
        } else if has_override {
            Step::Fail
        } else {
            Step::Next(Machine { state: State::PathStart, ..m }, p - 1)
        }
    } else {
        Step::Fail
    }
}

pub open spec fn step_file(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    let url = UrlRecord { scheme: s_file(), host: Some(Host::Empty), ..url };
    if c_is(input, p, b'/') || c_is(input, p, b'\\') {
        Step::Next(Machine { state: State::FileSlash, url, ..m }, p)
    } else if base is Some && base->0.scheme == s_file() {
        let b = base->0;
        let url = UrlRecord { host: b.host, path: b.path, query: b.query, ..url };
        if c_is(input, p, b'?') {
            Step::Next(
                Machine {
                    state: State::Query,
                    url: UrlRecord { query: Some(Seq::empty()), ..url },
                    ..m
                },
                p,
            )
        } else if c_is(input, p, b'#') {
            Step::Next(
                Machine {
                    state: State::Fragment,
                    url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                    ..m
                },
                p,
            )
        } else if !eof {
            let url = UrlRecord { query: None, ..url };
            let url = if !starts_with_windows_drive_letter(input.skip(p)) {
                shorten_path(url)
            } else {
                UrlRecord { path: UrlPath::List(Seq::empty()), ..url }
            };
            Step::Next(Machine { state: State::Path, url, ..m }, p - 1)
        } else {
            Step::Next(Machine { url, ..m }, p)
        }
    } else {
        Step::Next(Machine { state: State::Path, url, ..m }, p - 1)
    }
}

pub open spec fn step_file_slash(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if c_is(input, p, b'/') || c_is(input, p, b'\\') {
        Step::Next(Machine { state: State::FileHost, ..m }, p)
    } else {
        let url = if base is Some && base->0.scheme == s_file() {
            let b = base->0;
            let url = UrlRecord { host: b.host, ..url };
            match b.path {
                UrlPath::List(bsegs) => if !starts_with_windows_drive_letter(input.skip(p))
                    && bsegs.len() > 0 && is_normalized_windows_drive_letter(bsegs[0]) {
                    push_segment(url, bsegs[0])
                } else {
                    url
                },
                UrlPath::Opaque(_) => url,
            }
        } else {
            url
        };
        Step::Next(Machine { state: State::Path, url, ..m }, p - 1)
    }
}

pub open spec fn step_file_host(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if eof || c == b'/' || c == b'\\' || c == b'?' || c == b'#' {
        if !has_override && is_windows_drive_letter(m.buffer) {
            Step::Next(Machine { state: State::Path, ..m }, p - 1)
        } else if m.buffer.len() == 0 {
            let url = UrlRecord { host: Some(Host::Empty), ..url };
            if has_override {
                Step::Return(url)
            } else {
                Step::Next(Machine { url, state: State::PathStart, ..m }, p - 1)
            }
        } else {
            match host_parse(m.buffer, !special) {
                None => Step::Fail,
                Some(h) => {
                    let h = if h == Host::Domain(s_localhost()) {
                        Host::Empty
                    } else {
                        h
                    };
                    let url = UrlRecord { host: Some(h), ..url };
                    if has_override {
                        Step::Return(url)
                    } else {
                        Step::Next(
                            Machine {
                                url,
                                buffer: Seq::empty(),
                                state: State::PathStart,
                                ..m
                            },
                            p - 1,
                        )
                    }
                },
            }
        }
    } else {
        Step::Next(Machine { buffer: m.buffer.push(c), ..m }, p)
    }
}

pub open spec fn step_path_start(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if special {
        if !c_is(input, p, b'/') && !c_is(input, p, b'\\') {
            Step::Next(Machine { state: State::Path, ..m }, p - 1)
        } else {
            Step::Next(Machine { state: State::Path, ..m }, p)
        }
    } else if !has_override && c_is(input, p, b'?') {
        Step::Next(
            Machine {
                state: State::Query,
                url: UrlRecord { query: Some(Seq::empty()), ..url },
                ..m
            },
            p,
        )
    } else if !has_override && c_is(input, p, b'#') {
        Step::Next(
            Machine {
                state: State::Fragment,
                url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                ..m
            },
            p,
        )
    } else if !eof {
        if c != b'/' {
            Step::Next(Machine { state: State::Path, ..m }, p - 1)
        } else {
            Step::Next(Machine { state: State::Path, ..m }, p)
        }
    } else if has_override && url.host is None {
        Step::Next(Machine { url: push_segment(url, Seq::empty()), ..m }, p)
    } else {
        Step::Next(m, p)
    }
}

pub open spec fn step_path(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    let slash = c_is(input, p, b'/') || (special && c_is(input, p, b'\\'));
    if eof || slash || (!has_override && (c == b'?' || c == b'#')) {
        let buffer = m.buffer;
        let url = if is_double_dot_segment(buffer) {
            let url = shorten_path(url);
            if !slash {
                push_segment(url, Seq::empty())
            } else {
                url
            }
        } else if is_single_dot_segment(buffer) && !slash {
            push_segment(url, Seq::empty())
        } else if !is_single_dot_segment(buffer) {
            let buffer = if url.scheme == s_file() && path_is_empty_list(url)
                && is_windows_drive_letter(buffer) {
                buffer.update(1, b':')
            } else {
                buffer
            };
            push_segment(url, buffer)
        } else {
            url
        };
        let m = Machine { url, buffer: Seq::empty(), ..m };
        if c_is(input, p, b'?') {
            Step::Next(
                Machine {
                    state: State::Query,
                    url: UrlRecord { query: Some(Seq::empty()), ..url },
                    ..m
                },
                p,
            )
        } else if c_is(input, p, b'#') {
            Step::Next(
                Machine {
                    state: State::Fragment,
                    url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                    ..m
                },
                p,
            )
        } else {
            Step::Next(m, p)
        }
    } else {
        Step::Next(Machine { buffer: m.buffer + pe(c, EncodeSet::Path), ..m }, p)
    }
}

pub open spec fn step_opaque_path(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if c_is(input, p, b'?') {
        Step::Next(
            Machine {
                state: State::Query,
                url: UrlRecord { query: Some(Seq::empty()), ..url },
                ..m
            },
            p,
        )
    } else if c_is(input, p, b'#') {
        Step::Next(
            Machine {
                state: State::Fragment,
                url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                ..m
            },
            p,
        )
    } else if !eof {
        let add = if c == b' ' {
            if remaining_starts_with(input, p, b'?') || remaining_starts_with(input, p, b'#') {
                seq![b'%', b'2', b'0']
            } else {
                seq![b' ']
            }
        } else {
            pe(c, EncodeSet::C0Control)
        };
        let path = match url.path {
            UrlPath::Opaque(s) => UrlPath::Opaque(s + add),
            UrlPath::List(l) => UrlPath::List(l),  // unreachable
        };
        Step::Next(Machine { url: UrlRecord { path, ..url }, ..m }, p)
    } else {
        Step::Next(m, p)
    }
}

pub open spec fn step_query(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if (!has_override && c_is(input, p, b'#')) || eof {
        let set = if special {
            EncodeSet::SpecialQuery
        } else {
            EncodeSet::Query
        };
        let q = match url.query {
            Some(q) => q,
            None => Seq::empty(),  // unreachable: set on entry
        };
        let url = UrlRecord { query: Some(q + pe_seq(m.buffer, set)), ..url };
        let m = Machine { url, buffer: Seq::empty(), ..m };
        if c_is(input, p, b'#') {
            Step::Next(
                Machine {
                    state: State::Fragment,
                    url: UrlRecord { fragment: Some(Seq::empty()), ..url },
                    ..m
                },
                p,
            )
        } else {
            Step::Next(m, p)
        }
    } else {
        Step::Next(Machine { buffer: m.buffer.push(c), ..m }, p)
    }
}

pub open spec fn step_fragment(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    if !eof {
        let f = match url.fragment {
            Some(f) => f,
            None => Seq::empty(),  // unreachable: set on entry
        };
        Step::Next(
            Machine {
                url: UrlRecord { fragment: Some(f + pe(c, EncodeSet::Fragment)), ..url },
                ..m
            },
            p,
        )
    } else {
        Step::Next(m, p)
    }
}

/// Runs the state `m.state` on the code point at `p` (EOF if `p` is past the
/// end of `input`).
pub open spec fn step(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Step {
    let url = m.url;
    let has_override = state_override is Some;
    let eof = is_eof(input, p);
    let c: u8 = if eof {
        0
    } else {
        input[p]
    };
    let special = is_special(url);
    match m.state {
        State::SchemeStart => step_scheme_start(input, base, state_override, m, p),
        State::Scheme => step_scheme(input, base, state_override, m, p),
        State::NoScheme => step_no_scheme(input, base, state_override, m, p),
        State::SpecialRelativeOrAuthority => step_special_relative_or_authority(input, base, state_override, m, p),
        State::PathOrAuthority => step_path_or_authority(input, base, state_override, m, p),
        State::Relative => step_relative(input, base, state_override, m, p),
        State::RelativeSlash => step_relative_slash(input, base, state_override, m, p),
        State::SpecialAuthoritySlashes => step_special_authority_slashes(input, base, state_override, m, p),
        State::SpecialAuthorityIgnoreSlashes => step_special_authority_ignore_slashes(input, base, state_override, m, p),
        State::Authority => step_authority(input, base, state_override, m, p),
        State::Host | State::Hostname => step_host(input, base, state_override, m, p),
        State::Port => step_port(input, base, state_override, m, p),
        State::File => step_file(input, base, state_override, m, p),
        State::FileSlash => step_file_slash(input, base, state_override, m, p),
        State::FileHost => step_file_host(input, base, state_override, m, p),
        State::PathStart => step_path_start(input, base, state_override, m, p),
        State::Path => step_path(input, base, state_override, m, p),
        State::OpaquePath => step_opaque_path(input, base, state_override, m, p),
        State::Query => step_query(input, base, state_override, m, p),
        State::Fragment => step_fragment(input, base, state_override, m, p),
    }
}

/// Termination measure: rewinding the pointer (scheme state's "start over",
/// the authority state's rewind) only ever moves to a lower phase.
pub open spec fn phase(s: State) -> nat {
    match s {
        State::SchemeStart | State::Scheme => 2,
        State::NoScheme | State::SpecialRelativeOrAuthority | State::PathOrAuthority
        | State::Relative | State::RelativeSlash | State::SpecialAuthoritySlashes
        | State::SpecialAuthorityIgnoreSlashes | State::Authority | State::File
        | State::FileSlash => 1,
        _ => 0,
    }
}

/// Termination measure: a state that leaves the pointer where it is
/// ("decrease pointer by 1") always moves to a lower rank.
pub open spec fn rank(s: State) -> nat {
    match s {
        State::SchemeStart => 6,
        State::Scheme => 6,
        State::NoScheme => 5,
        State::SpecialRelativeOrAuthority => 5,
        State::SpecialAuthoritySlashes => 5,
        State::PathOrAuthority => 4,
        State::Relative => 4,
        State::RelativeSlash => 4,
        State::File => 4,
        State::FileSlash => 4,
        State::SpecialAuthorityIgnoreSlashes => 3,
        State::Authority => 2,
        State::Host => 6,
        State::Hostname => 6,
        State::Port => 5,
        State::FileHost => 5,
        State::PathStart => 4,
        State::Path => 3,
        State::OpaquePath => 2,
        State::Query => 2,
        State::Fragment => 2,
    }
}

/// "Keep running the state machine by switching on state. If after a run
/// pointer points to the EOF code point, go to the next step. Otherwise,
/// increase pointer by 1 and continue with the state machine."
pub open spec fn run(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> Option<UrlRecord>
    decreases phase(m.state), input.len() - p, rank(m.state),
{
    if p < 0 || p > input.len() {
        None  // unreachable
    } else {
        match step(input, base, state_override, m, p) {
            Step::Fail => None,
            Step::Return(url) => Some(url),
            Step::Next(m2, p2) => if p2 >= input.len() {
                Some(m2.url)
            } else if p2 + 1 < 0 {
                None  // unreachable: the authority state rewinds at most to its start
            } else {
                run(input, base, state_override, m2, p2 + 1)
            }
        }
    }
}

/// Removes leading and trailing C0 control or space.
pub open spec fn trim_c0_space(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && is_c0_control_or_space(s[0]) {
        trim_c0_space(s.skip(1))
    } else if s.len() > 0 && is_c0_control_or_space(s.last()) {
        trim_c0_space(s.drop_last())
    } else {
        s
    }
}

/// Removes all ASCII tab or newline.
pub open spec fn remove_tab_newline(s: Seq<u8>) -> Seq<u8> {
    s.filter(|c: u8| !is_ascii_tab_or_newline(c))
}

pub open spec fn initial_machine(state: State, url: UrlRecord) -> Machine {
    Machine {
        state,
        url,
        buffer: Seq::empty(),
        at_sign_seen: false,
        inside_brackets: false,
        password_token_seen: false,
    }
}

/// The basic URL parser, without url or state override.
pub open spec fn parse_url(input: Seq<u8>, base: Option<UrlRecord>) -> Option<UrlRecord> {
    let input = remove_tab_newline(trim_c0_space(input));
    run(input, base, None, initial_machine(State::SchemeStart, new_url()), 0)
}

/// The basic URL parser with url and state override: the URL it leaves
/// behind, or `None` on failure.
pub open spec fn parse_url_override(input: Seq<u8>, url: UrlRecord, state: State) -> Option<
    UrlRecord,
> {
    let input = remove_tab_newline(input);
    run(input, None, Some(state), initial_machine(state, url), 0)
}

// ---------------------------------------------------------------------------
// The URL serializer (§4.5)
// ---------------------------------------------------------------------------

pub open spec fn path_serialize(path: UrlPath) -> Seq<u8> {
    match path {
        UrlPath::Opaque(s) => s,
        UrlPath::List(segs) => segments_serialize(segs),
    }
}

pub open spec fn segments_serialize(segs: Seq<Seq<u8>>) -> Seq<u8>
    decreases segs.len(),
{
    if segs.len() == 0 {
        Seq::empty()
    } else {
        segments_serialize(segs.drop_last()) + seq![b'/'] + segs.last()
    }
}

/// Username, ":" and password if the password is non-empty, and "@", if
/// the URL includes credentials.
pub open spec fn credentials_serialize(url: UrlRecord) -> Seq<u8> {
    if includes_credentials(url) {
        url.username + (if url.password.len() > 0 {
            seq![b':'] + url.password
        } else {
            Seq::empty()
        }) + seq![b'@']
    } else {
        Seq::empty()
    }
}

/// ":" and the port, if the port is non-null.
pub open spec fn port_serialize(url: UrlRecord) -> Seq<u8> {
    match url.port {
        Some(n) => seq![b':'] + decimal(n as nat),
        None => Seq::empty(),
    }
}

/// "//", credentials, host and port, if the host is non-null.
pub open spec fn authority_serialize(url: UrlRecord) -> Seq<u8> {
    match url.host {
        None => Seq::empty(),
        Some(h) => seq![b'/', b'/'] + credentials_serialize(url) + host_serialize(h)
            + port_serialize(url),
    }
}

pub open spec fn query_serialize(url: UrlRecord) -> Seq<u8> {
    match url.query {
        Some(q) => seq![b'?'] + q,
        None => Seq::empty(),
    }
}

pub open spec fn fragment_serialize(url: UrlRecord) -> Seq<u8> {
    match url.fragment {
        Some(f) => seq![b'#'] + f,
        None => Seq::empty(),
    }
}

/// Whether the serializer inserts "/." before the path.
pub open spec fn needs_dot_slash(url: UrlRecord) -> bool {
    match url.path {
        UrlPath::List(segs) => url.host is None && segs.len() > 1 && segs[0].len() == 0,
        UrlPath::Opaque(_) => false,
    }
}

/// The URL serializer.
pub open spec fn serialize(url: UrlRecord, exclude_fragment: bool) -> Seq<u8> {
    url.scheme + seq![b':'] + authority_serialize(url) + (if needs_dot_slash(url) {
        seq![b'/', b'.']
    } else {
        Seq::empty()
    }) + path_serialize(url.path) + query_serialize(url) + (if exclude_fragment {
        Seq::empty()
    } else {
        fragment_serialize(url)
    })
}

// ---------------------------------------------------------------------------
// The API's setters (§6.1)
// ---------------------------------------------------------------------------

/// `run`, returning the URL the parser leaves behind instead of its
/// result. The setters below ignore the basic URL parser's return value: it
/// changes their URL in place, and what it changed stays changed even when
/// it then returns failure. Returning `m.url` on `Step::Fail` is exact
/// because no state changes the URL in the same step that it returns
/// failure (each "return failure" comes before that state's changes).
pub open spec fn run_url(
    input: Seq<u8>,
    base: Option<UrlRecord>,
    state_override: Option<State>,
    m: Machine,
    p: int,
) -> UrlRecord
    decreases phase(m.state), input.len() - p, rank(m.state),
{
    if p < 0 || p > input.len() {
        m.url  // unreachable
    } else {
        match step(input, base, state_override, m, p) {
            Step::Fail => m.url,
            Step::Return(url) => url,
            Step::Next(m2, p2) => if p2 >= input.len() {
                m2.url
            } else if p2 + 1 < 0 {
                m2.url  // unreachable
            } else {
                run_url(input, base, state_override, m2, p2 + 1)
            },
        }
    }
}

/// "Basic URL parse `input` with `url` as url and `state` as state
/// override": the URL afterwards.
pub open spec fn override_url(input: Seq<u8>, url: UrlRecord, state: State) -> UrlRecord {
    run_url(remove_tab_newline(input), None, Some(state), initial_machine(state, url), 0)
}

/// "A URL cannot have a username/password/port if its host is null or the
/// empty string, or its scheme is "file"."
pub open spec fn cannot_have_credentials_or_port(url: UrlRecord) -> bool {
    url.host is None || url.host == Some(Host::Empty) || url.scheme == s_file()
}

/// The protocol setter: "basic URL parse the given value, followed by U+003A
/// (:), with this's URL as url and scheme start state as state override."
pub open spec fn set_protocol(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    override_url(value.push(b':'), url, State::SchemeStart)
}

/// The username setter: "If this's URL cannot have a username/password/port,
/// then return. Set the username given this's URL and the given value",
/// which UTF-8 percent-encodes it with the userinfo set.
pub open spec fn set_username(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if cannot_have_credentials_or_port(url) {
        url
    } else {
        UrlRecord { username: pe_seq(value, EncodeSet::Userinfo), ..url }
    }
}

/// The password setter, as the username setter.
pub open spec fn set_password(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if cannot_have_credentials_or_port(url) {
        url
    } else {
        UrlRecord { password: pe_seq(value, EncodeSet::Userinfo), ..url }
    }
}

/// The host setter: "If this's URL has an opaque path, then return. Basic
/// URL parse the given value with this's URL as url and host state as state
/// override."
pub open spec fn set_host(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if url.path is Opaque {
        url
    } else {
        override_url(value, url, State::Host)
    }
}

/// The hostname setter: as the host setter, with hostname state.
pub open spec fn set_hostname(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if url.path is Opaque {
        url
    } else {
        override_url(value, url, State::Hostname)
    }
}

/// The port setter: "If this's URL cannot have a username/password/port,
/// then return. If the given value is the empty string, then set this's
/// URL's port to null. Otherwise, basic URL parse the given value with this's
/// URL as url and port state as state override."
pub open spec fn set_port(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if cannot_have_credentials_or_port(url) {
        url
    } else if value.len() == 0 {
        UrlRecord { port: None, ..url }
    } else {
        override_url(value, url, State::Port)
    }
}

/// The pathname setter: "If this's URL has an opaque path, then return.
/// Empty this's URL's path. Basic URL parse the given value with this's URL
/// as url and path start state as state override."
pub open spec fn set_pathname(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if url.path is Opaque {
        url
    } else {
        override_url(value, UrlRecord { path: UrlPath::List(Seq::empty()), ..url }, State::PathStart)
    }
}

/// The given value without one leading `c`.
pub open spec fn strip_leading(value: Seq<u8>, c: u8) -> Seq<u8> {
    if value.len() > 0 && value[0] == c {
        value.skip(1)
    } else {
        value
    }
}

/// The search setter: "If the given value is the empty string, set url's
/// query to null and return. Let input be the given value with a single
/// leading U+003F (?) removed, if any. Set url's query to the empty string.
/// Basic URL parse input with url as url and query state as state
/// override." (Its effects on the URLSearchParams object are not modelled.)
pub open spec fn set_search(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if value.len() == 0 {
        UrlRecord { query: None, ..url }
    } else {
        override_url(strip_leading(value, b'?'), UrlRecord { query: Some(Seq::empty()), ..url }, State::Query)
    }
}

/// The hash setter: as the search setter, with "#", the fragment and
/// fragment state.
pub open spec fn set_hash(url: UrlRecord, value: Seq<u8>) -> UrlRecord {
    if value.len() == 0 {
        UrlRecord { fragment: None, ..url }
    } else {
        override_url(strip_leading(value, b'#'), UrlRecord { fragment: Some(Seq::empty()), ..url }, State::Fragment)
    }
}

} // verus!
