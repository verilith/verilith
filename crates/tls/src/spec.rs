//! The specification: the TLS 1.3 wire formats this crate parses, written
//! from RFC 8446 as pure functions over the bytes. Everything here is
//! trusted: it is what the proofs prove the code computes. Read it against
//! the RFC; the section of each definition is given.
//!
//! The functions work on positions in one byte string, so that what they
//! return (spans `(start, end)`, half open) are positions the parser can
//! hand out without copying. A vector `<a..b>` (§3.4) at `pos` inside an
//! enclosing structure that ends at `end` is a length prefix of 1, 2 or 3
//! bytes, followed by that many bytes, all before `end`.
//!
//! Where the RFC leaves a choice to the implementation, the spec makes the
//! one rustls makes, and says so.
#[cfg(verus_only)]
use verilith_core::bytes::be16;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Vectors (§3.4)
// ---------------------------------------------------------------------------

/// A vector with a 1-byte length at `pos`, inside `[.., end)`: the span of
/// its contents.
pub open spec fn vec8(b: Seq<u8>, pos: int, end: int) -> Option<(int, int)> {
    if 0 <= pos && pos + 1 <= end && end <= b.len() && pos + 1 + b[pos] as int <= end {
        Some((pos + 1, pos + 1 + b[pos] as int))
    } else {
        None
    }
}

/// A vector with a 2-byte length at `pos`, inside `[.., end)`.
pub open spec fn vec16(b: Seq<u8>, pos: int, end: int) -> Option<(int, int)> {
    if 0 <= pos && pos + 2 <= end && end <= b.len() && pos + 2 + be16(b, pos) <= end {
        Some((pos + 2, pos + 2 + be16(b, pos)))
    } else {
        None
    }
}

/// The big-endian value of the 3 bytes at `i` (`uint24`).
pub open spec fn be24(b: Seq<u8>, i: int) -> nat {
    (b[i] as nat * 256 + b[i + 1] as nat) * 256 + b[i + 2] as nat
}

/// A vector with a 2-byte length at `s` that is exactly the bytes
/// `[s, e)` (its contents end at `e`), and its contents.
pub open spec fn whole16(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match vec16(b, s, e) {
        Some((ls, le)) => if le == e { Some((ls, le)) } else { None },
        None => None,
    }
}

/// The same with a 1-byte length.
pub open spec fn whole8(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match vec8(b, s, e) {
        Some((ls, le)) => if le == e { Some((ls, le)) } else { None },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The record layer (§5.1)
// ---------------------------------------------------------------------------

/// `ContentType` values (§5.1, §B.1).
pub const CT_CHANGE_CIPHER_SPEC: u8 = 20;

pub const CT_ALERT: u8 = 21;

pub const CT_HANDSHAKE: u8 = 22;

pub const CT_APPLICATION_DATA: u8 = 23;

/// Length of a record header: type, legacy_record_version, length.
pub const RECORD_HEADER_LEN: usize = 5;

/// The largest `TLSPlaintext.fragment`: 2^14 bytes.
pub const MAX_PLAINTEXT: usize = 16384;

/// The largest `TLSCiphertext.encrypted_record`: 2^14 + 256 bytes.
pub const MAX_CIPHERTEXT: usize = 16640;

/// A record header (§5.1, §5.2).
pub struct SpecRecordHeader {
    pub content_type: u8,
    pub legacy_version: u16,
    pub length: nat,
}

/// The header of the record at the start of `b`, or `None` if `b` is
/// shorter than a header. `length` is not yet checked against a limit:
/// which limit applies (`MAX_PLAINTEXT` or `MAX_CIPHERTEXT`) depends on
/// whether the record is protected, which the caller knows (§5.1: a larger
/// record is a `record_overflow` alert).
pub open spec fn record_header(b: Seq<u8>) -> Option<SpecRecordHeader> {
    if b.len() < 5 {
        None
    } else {
        Some(
            SpecRecordHeader {
                content_type: b[0],
                legacy_version: be16(b, 1) as u16,
                length: be16(b, 3),
            },
        )
    }
}

// ---------------------------------------------------------------------------
// Handshake messages (§4)
// ---------------------------------------------------------------------------

/// `HandshakeType` values (§4).
pub const HT_CLIENT_HELLO: u8 = 1;

pub const HT_SERVER_HELLO: u8 = 2;

pub const HT_NEW_SESSION_TICKET: u8 = 4;

pub const HT_END_OF_EARLY_DATA: u8 = 5;

pub const HT_ENCRYPTED_EXTENSIONS: u8 = 8;

pub const HT_CERTIFICATE: u8 = 11;

pub const HT_CERTIFICATE_REQUEST: u8 = 13;

pub const HT_CERTIFICATE_VERIFY: u8 = 15;

pub const HT_FINISHED: u8 = 20;

pub const HT_KEY_UPDATE: u8 = 24;

pub const HT_MESSAGE_HASH: u8 = 254;

/// Length of a handshake message header: msg_type and a 24-bit length.
pub const HANDSHAKE_HEADER_LEN: usize = 4;

/// The handshake message at the start of `b` (§4): its type and the span
/// of its body, or `None` if `b` does not yet hold all of it.
pub open spec fn handshake_message(b: Seq<u8>) -> Option<(u8, (int, int))> {
    if b.len() < 4 || 4 + be24(b, 1) > b.len() {
        None
    } else {
        Some((b[0], (4int, 4 + be24(b, 1) as int)))
    }
}

// ---------------------------------------------------------------------------
// ClientHello (§4.1.2)
// ---------------------------------------------------------------------------

/// `ExtensionType` values this crate interprets (§4.2; RFC 6066 §3 for
/// server_name, RFC 7301 §3.1 for ALPN).
pub const EXT_SERVER_NAME: u16 = 0;

pub const EXT_SUPPORTED_GROUPS: u16 = 10;

pub const EXT_SIGNATURE_ALGORITHMS: u16 = 13;

pub const EXT_ALPN: u16 = 16;

pub const EXT_PRE_SHARED_KEY: u16 = 41;

pub const EXT_EARLY_DATA: u16 = 42;

/// encrypted_client_hello (RFC 9849 §5).
pub const EXT_ECH: u16 = 0xfe0d;

pub const EXT_SUPPORTED_VERSIONS: u16 = 43;

pub const EXT_COOKIE: u16 = 44;

pub const EXT_PSK_KEY_EXCHANGE_MODES: u16 = 45;

pub const EXT_SIGNATURE_ALGORITHMS_CERT: u16 = 50;

pub const EXT_KEY_SHARE: u16 = 51;

/// One `Extension` (§4.2): its type and the span of `extension_data`.
pub struct SpecExt {
    pub typ: u16,
    pub data: (int, int),
}

/// The extensions from `pos` to exactly `end` (§4.2): each a 2-byte type
/// and a vector `extension_data<0..2^16-1>`, back to back.
pub open spec fn parse_exts(b: Seq<u8>, pos: int, end: int) -> Option<Seq<SpecExt>>
    decreases end - pos,
{
    if pos == end {
        Some(Seq::empty())
    } else if pos > end || pos + 2 > end {
        None
    } else {
        match vec16(b, pos + 2, end) {
            None => None,
            Some((s, e)) => match parse_exts(b, e, end) {
                None => None,
                Some(rest) => Some(seq![SpecExt { typ: be16(b, pos) as u16, data: (s, e) }] + rest),
            },
        }
    }
}

/// The fields of a ClientHello before its extensions are interpreted.
pub struct SpecOuter {
    pub legacy_version: u16,
    /// `random` is always `[2, 34)`.
    pub session_id: (int, int),
    pub cipher_suites: (int, int),
    pub compression_methods: (int, int),
    /// The contents of the `extensions` vector; `(n, n)` when the
    /// ClientHello has none.
    pub extensions: (int, int),
    pub exts: Seq<SpecExt>,
}

/// The syntax of a ClientHello body `b` (§4.1.2):
///
/// ```text
/// struct {
///     ProtocolVersion legacy_version = 0x0303;
///     Random random;                                  // 32 bytes
///     opaque legacy_session_id<0..32>;
///     CipherSuite cipher_suites<2..2^16-2>;           // 2 bytes each
///     opaque legacy_compression_methods<1..2^8-1>;
///     Extension extensions<8..2^16-1>;
/// } ClientHello;
/// ```
///
/// The body must end exactly where the structure does. As the RFC allows
/// (§4.1.2, "TLS 1.3 servers might receive ClientHello messages without an
/// extensions field from prior versions of TLS"), the extensions vector may
/// be absent, which is read as no extensions. Its lower bound of 8 is not
/// checked here, as rustls does not: a TLS 1.3 ClientHello must carry
/// supported_versions, which negotiation checks, and a TLS 1.2 one need not
/// meet it.
pub open spec fn parse_outer(b: Seq<u8>) -> Option<SpecOuter> {
    let n = b.len() as int;
    if n < 35 {
        None
    } else {
        match vec8(b, 34, n) {
            None => None,
            Some((ss, se)) => if se - ss > 32 {
                None
            } else {
                match vec16(b, se, n) {
                    None => None,
                    Some((cs, ce)) => if (ce - cs) % 2 != 0 || ce - cs < 2 {
                        None
                    } else {
                        match vec8(b, ce, n) {
                            None => None,
                            Some((ms, me)) => if me - ms < 1 {
                                None
                            } else if me == n {
                                Some(
                                    SpecOuter {
                                        legacy_version: be16(b, 0) as u16,
                                        session_id: (ss, se),
                                        cipher_suites: (cs, ce),
                                        compression_methods: (ms, me),
                                        extensions: (n, n),
                                        exts: Seq::empty(),
                                    },
                                )
                            } else {
                                match whole16(b, me, n) {
                                    None => None,
                                    Some((xs, xe)) => match parse_exts(b, xs, xe) {
                                        None => None,
                                        Some(exts) => Some(
                                            SpecOuter {
                                                legacy_version: be16(b, 0) as u16,
                                                session_id: (ss, se),
                                                cipher_suites: (cs, ce),
                                                compression_methods: (ms, me),
                                                extensions: (xs, xe),
                                                exts,
                                            },
                                        ),
                                    },
                                }
                            },
                        }
                    },
                }
            },
        }
    }
}

/// The data of the first extension of type `t` in `exts`.
pub open spec fn find_ext(exts: Seq<SpecExt>, t: u16) -> Option<(int, int)>
    decreases exts.len(),
{
    if exts.len() == 0 {
        None
    } else if exts[0].typ == t {
        Some(exts[0].data)
    } else {
        find_ext(exts.drop_first(), t)
    }
}

/// §4.2: "There MUST NOT be more than one extension of the same type in a
/// given extension block."
pub open spec fn exts_distinct(exts: Seq<SpecExt>) -> bool {
    forall|i: int, j: int| 0 <= i < j < exts.len() ==> exts[i].typ != exts[j].typ
}

/// §4.2.11: pre_shared_key "MUST be the last extension in the
/// ClientHello".
pub open spec fn psk_last(exts: Seq<SpecExt>) -> bool {
    forall|i: int| 0 <= i < exts.len() - 1 ==> exts[i].typ != EXT_PRE_SHARED_KEY
}

// ---- Extension contents ----------------------------------------------------

/// A list of 2-byte values in a vector with a 2-byte length that is the
/// whole of `[s, e)`, at least one value: supported_groups
/// (`NamedGroup named_group_list<2..2^16-1>`, §4.2.7), signature_algorithms
/// and signature_algorithms_cert (`SignatureScheme
/// supported_signature_algorithms<2..2^16-2>`, §4.2.3).
pub open spec fn u16_list(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match whole16(b, s, e) {
        Some((ls, le)) => if (le - ls) % 2 == 0 && le - ls >= 2 { Some((ls, le)) } else { None },
        None => None,
    }
}

/// supported_versions in a ClientHello (§4.2.1):
/// `ProtocolVersion versions<2..254>`.
pub open spec fn versions_list(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match whole8(b, s, e) {
        Some((ls, le)) => if (le - ls) % 2 == 0 && le - ls >= 2 { Some((ls, le)) } else { None },
        None => None,
    }
}

/// psk_key_exchange_modes (§4.2.9): `PskKeyExchangeMode ke_modes<1..255>`.
pub open spec fn psk_modes_list(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match whole8(b, s, e) {
        Some((ls, le)) => if le - ls >= 1 { Some((ls, le)) } else { None },
        None => None,
    }
}

/// cookie (§4.2.2): `opaque cookie<1..2^16-1>`.
pub open spec fn cookie_value(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match whole16(b, s, e) {
        Some((ls, le)) => if le - ls >= 1 { Some((ls, le)) } else { None },
        None => None,
    }
}

/// The `ServerName` entries from `pos` to exactly `end` (RFC 6066 §3),
/// given the host name found so far:
///
/// ```text
/// struct {
///     NameType name_type;              // 1 byte
///     select (name_type) {
///         case host_name: HostName;    // opaque HostName<1..2^16-1>
///     } name;
/// } ServerName;
/// ```
///
/// RFC 6066 defines only `host_name` (0) and says the list "MUST NOT
/// contain more than one name of the same name_type". The body of an
/// unknown type is undefined; like rustls, it is read as a vector with a
/// 2-byte length and ignored.
pub open spec fn server_names(b: Seq<u8>, pos: int, end: int, found: Option<(int, int)>) -> Option<
    Option<(int, int)>,
>
    decreases end - pos,
{
    if pos == end {
        Some(found)
    } else if pos > end {
        None
    } else {
        match vec16(b, pos + 1, end) {
            None => None,
            Some((s, e)) => if b[pos] == 0 {
                if found is Some || e - s < 1 {
                    None
                } else {
                    server_names(b, e, end, Some((s, e)))
                }
            } else {
                server_names(b, e, end, found)
            },
        }
    }
}

/// server_name (RFC 6066 §3): `ServerName server_name_list<1..2^16-1>`,
/// and the span of its host name, if it has one.
pub open spec fn server_name(b: Seq<u8>, s: int, e: int) -> Option<Option<(int, int)>> {
    match whole16(b, s, e) {
        Some((ls, le)) => if le - ls >= 1 { server_names(b, ls, le, None) } else { None },
        None => None,
    }
}

/// ALPN protocol names from `pos` to exactly `end` (RFC 7301 §3.1): each
/// `opaque ProtocolName<1..2^8-1>`.
pub open spec fn protocol_names(b: Seq<u8>, pos: int, end: int) -> bool
    decreases end - pos,
{
    if pos == end {
        true
    } else if pos > end {
        false
    } else {
        match vec8(b, pos, end) {
            None => false,
            Some((s, e)) => e - s >= 1 && protocol_names(b, e, end),
        }
    }
}

/// application_layer_protocol_negotiation (RFC 7301 §3.1):
/// `ProtocolName protocol_name_list<2..2^16-1>`. The span of the list's
/// contents.
pub open spec fn alpn_list(b: Seq<u8>, s: int, e: int) -> Option<(int, int)> {
    match whole16(b, s, e) {
        Some((ls, le)) => if le - ls >= 2 && protocol_names(b, ls, le) {
            Some((ls, le))
        } else {
            None
        },
        None => None,
    }
}

/// `KeyShareEntry`s from `pos` to exactly `end` (§4.2.8), their groups in
/// order:
///
/// ```text
/// struct {
///     NamedGroup group;                    // 2 bytes
///     opaque key_exchange<1..2^16-1>;
/// } KeyShareEntry;
/// ```
pub open spec fn key_share_entries(b: Seq<u8>, pos: int, end: int) -> Option<Seq<u16>>
    decreases end - pos,
{
    if pos == end {
        Some(Seq::empty())
    } else if pos > end || pos + 2 > end {
        None
    } else {
        match vec16(b, pos + 2, end) {
            None => None,
            Some((s, e)) => if e - s < 1 {
                None
            } else {
                match key_share_entries(b, e, end) {
                    None => None,
                    Some(rest) => Some(seq![be16(b, pos) as u16] + rest),
                }
            },
        }
    }
}

/// key_share in a ClientHello (§4.2.8):
/// `KeyShareEntry client_shares<0..2^16-1>`. The span of its contents and
/// the groups of its entries.
pub open spec fn key_share_list(b: Seq<u8>, s: int, e: int) -> Option<((int, int), Seq<u16>)> {
    match whole16(b, s, e) {
        Some((ls, le)) => match key_share_entries(b, ls, le) {
            Some(g) => Some(((ls, le), g)),
            None => None,
        },
        None => None,
    }
}

/// §4.2.8: "Clients MUST NOT offer multiple KeyShareEntry values for the
/// same group." Servers may check it; rustls does, and so does this crate.
pub open spec fn groups_distinct(g: Seq<u16>) -> bool {
    forall|i: int, j: int| 0 <= i < j < g.len() ==> g[i] != g[j]
}

/// `PskIdentity`s from `pos` to exactly `end` (§4.2.11), and how many:
/// each `opaque identity<1..2^16-1>` and a 4-byte `obfuscated_ticket_age`.
pub open spec fn psk_identities(b: Seq<u8>, pos: int, end: int) -> Option<nat>
    decreases end - pos,
{
    if pos == end {
        Some(0)
    } else if pos > end {
        None
    } else {
        match vec16(b, pos, end) {
            None => None,
            Some((s, e)) => if e - s < 1 || e + 4 > end {
                None
            } else {
                match psk_identities(b, e + 4, end) {
                    None => None,
                    Some(k) => Some(k + 1),
                }
            },
        }
    }
}

/// `PskBinderEntry`s from `pos` to exactly `end` (§4.2.11), and how many:
/// each `opaque PskBinderEntry<32..255>`.
pub open spec fn psk_binders(b: Seq<u8>, pos: int, end: int) -> Option<nat>
    decreases end - pos,
{
    if pos == end {
        Some(0)
    } else if pos > end {
        None
    } else {
        match vec8(b, pos, end) {
            None => None,
            Some((s, e)) => if e - s < 32 {
                None
            } else {
                match psk_binders(b, e, end) {
                    None => None,
                    Some(k) => Some(k + 1),
                }
            },
        }
    }
}

/// pre_shared_key in a ClientHello (§4.2.11):
///
/// ```text
/// struct {
///     PskIdentity identities<7..2^16-1>;
///     PskBinderEntry binders<33..2^16-1>;
/// } OfferedPsks;
/// ```
///
/// The spans of the two lists' contents. The binders vector starts at the
/// first byte not covered by the binder computation (§4.2.11.2), so a
/// server computes binders over the ClientHello up to `binders.0 - 2`.
/// There must be as many binders as identities: the RFC requires a binder
/// "for each entry in the identities list".
pub open spec fn offered_psks(b: Seq<u8>, s: int, e: int) -> Option<((int, int), (int, int))> {
    match vec16(b, s, e) {
        None => None,
        Some((is, ie)) => match whole16(b, ie, e) {
            None => None,
            Some((bs, be)) => if ie - is < 7 || be - bs < 33 {
                None
            } else {
                match (psk_identities(b, is, ie), psk_binders(b, bs, be)) {
                    (Some(k1), Some(k2)) => if k1 == k2 { Some(((is, ie), (bs, be))) } else { None },
                    _ => None,
                }
            },
        }
    }
}

/// A span inside an optional extension: `None` when the extension is
/// absent, `Some(None)` when it is present and malformed.
pub open spec fn opt<T>(x: Option<(int, int)>, f: spec_fn(int, int) -> Option<T>) -> Option<
    Option<T>,
> {
    match x {
        None => Some(None),
        Some((s, e)) => match f(s, e) {
            None => None,
            Some(v) => Some(Some(v)),
        },
    }
}

/// A ClientHello, its extensions interpreted. Every span is a position in
/// the ClientHello body. Extensions this crate does not interpret are in
/// `outer.extensions`, uninterpreted, for the caller.
pub struct SpecHello {
    pub outer: SpecOuter,
    /// The host name in server_name, if there is one.
    pub server_name: Option<(int, int)>,
    /// The contents of `protocol_name_list`.
    pub alpn: Option<(int, int)>,
    /// The contents of `versions`.
    pub supported_versions: Option<(int, int)>,
    /// The contents of `named_group_list`.
    pub supported_groups: Option<(int, int)>,
    /// The contents of `supported_signature_algorithms`.
    pub signature_algorithms: Option<(int, int)>,
    pub signature_algorithms_cert: Option<(int, int)>,
    /// The contents of `client_shares`.
    pub key_shares: Option<(int, int)>,
    pub psk_modes: Option<(int, int)>,
    /// The contents of `identities` and of `binders`.
    pub pre_shared_key: Option<((int, int), (int, int))>,
    pub cookie: Option<(int, int)>,
    pub early_data: bool,
    /// The data of encrypted_client_hello, uninterpreted: ECH is the
    /// server's to decide on (`spec_ech`).
    pub ech: Option<(int, int)>,
}

/// The alert a malformed ClientHello is rejected with (§6.2).
pub enum SpecAlert {
    /// `decode_error`: "A message could not be decoded because some field
    /// was out of the specified range or the length of the message was
    /// incorrect."
    Decode,
    /// `illegal_parameter`: "A field in the handshake was incorrect or
    /// inconsistent with other fields."
    Illegal,
}

/// A ClientHello body, parsed and checked (§4.1.2, §4.2):
///
/// 1. Its syntax, `parse_outer`, or `decode_error`.
/// 2. No two extensions of one type, and pre_shared_key last, or
///    `illegal_parameter` (§4.2, §4.2.11).
/// 3. The contents of each extension this crate interprets, or
///    `decode_error`. early_data in a ClientHello is empty (§4.2.10).
/// 4. No two key shares for one group, or `illegal_parameter` (§4.2.8).
///
/// What a ClientHello must contain to negotiate TLS 1.3, and what its
/// values must be (legacy_version, a compression method list of exactly
/// `[0]`, supported_versions), is the state machine's concern, not the
/// parser's: a valid TLS 1.2 ClientHello parses.
pub open spec fn parse_client_hello(b: Seq<u8>) -> Result<SpecHello, SpecAlert> {
    match parse_outer(b) {
        None => Err(SpecAlert::Decode),
        Some(o) => if !exts_distinct(o.exts) || !psk_last(o.exts) {
            Err(SpecAlert::Illegal)
        } else {
            let x = o.exts;
            let sni = opt(find_ext(x, EXT_SERVER_NAME), |s: int, e: int| server_name(b, s, e));
            let alpn = opt(find_ext(x, EXT_ALPN), |s: int, e: int| alpn_list(b, s, e));
            let sv = opt(find_ext(x, EXT_SUPPORTED_VERSIONS), |s: int, e: int| versions_list(b, s, e));
            let sg = opt(find_ext(x, EXT_SUPPORTED_GROUPS), |s: int, e: int| u16_list(b, s, e));
            let sa = opt(find_ext(x, EXT_SIGNATURE_ALGORITHMS), |s: int, e: int| u16_list(b, s, e));
            let sac = opt(
                find_ext(x, EXT_SIGNATURE_ALGORITHMS_CERT),
                |s: int, e: int| u16_list(b, s, e),
            );
            let ks = opt(find_ext(x, EXT_KEY_SHARE), |s: int, e: int| key_share_list(b, s, e));
            let pm = opt(
                find_ext(x, EXT_PSK_KEY_EXCHANGE_MODES),
                |s: int, e: int| psk_modes_list(b, s, e),
            );
            let psk = opt(find_ext(x, EXT_PRE_SHARED_KEY), |s: int, e: int| offered_psks(b, s, e));
            let ck = opt(find_ext(x, EXT_COOKIE), |s: int, e: int| cookie_value(b, s, e));
            let ed = find_ext(x, EXT_EARLY_DATA);
            if sni is None || alpn is None || sv is None || sg is None || sa is None || sac is None
                || ks is None || pm is None || psk is None || ck is None || (ed matches Some(
                (s, e),
            ) && s != e) {
                Err(SpecAlert::Decode)
            } else if ks matches Some(Some((_, g))) && !groups_distinct(g) {
                Err(SpecAlert::Illegal)
            } else {
                Ok(
                    SpecHello {
                        outer: o,
                        server_name: match sni { Some(Some(h)) => h, _ => None },
                        alpn: alpn.unwrap(),
                        supported_versions: sv.unwrap(),
                        supported_groups: sg.unwrap(),
                        signature_algorithms: sa.unwrap(),
                        signature_algorithms_cert: sac.unwrap(),
                        key_shares: match ks { Some(Some((sp, _))) => Some(sp), _ => None },
                        psk_modes: pm.unwrap(),
                        pre_shared_key: psk.unwrap(),
                        cookie: ck.unwrap(),
                        early_data: ed is Some,
                        ech: find_ext(x, EXT_ECH),
                    },
                )
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Negotiation: what a TLS 1.3 server chooses from a ClientHello (§4.1.1)
// ---------------------------------------------------------------------------

/// `ProtocolVersion` of TLS 1.3 (§4.2.1).
pub const TLS13: u16 = 0x0304;

/// The 2-byte values in `[s, e)`, in order.
pub open spec fn u16s(b: Seq<u8>, s: int, e: int) -> Seq<u16> {
    Seq::new(((e - s) / 2) as nat, |i: int| be16(b, s + 2 * i) as u16)
}

/// The first of `prefs[i..]` that `offered` contains: the server's
/// preference wins, as in rustls (§4.1.1 leaves the choice to the server).
pub open spec fn first_in(prefs: Seq<u16>, i: int, offered: Seq<u16>) -> Option<u16>
    decreases prefs.len() - i,
{
    if i < 0 || i >= prefs.len() {
        None
    } else if offered.contains(prefs[i]) {
        Some(prefs[i])
    } else {
        first_in(prefs, i + 1, offered)
    }
}

/// The key_exchange of the first `KeyShareEntry` for group `g` in
/// `[pos, end)` (§4.2.8).
pub open spec fn find_share(b: Seq<u8>, pos: int, end: int, g: u16) -> Option<(int, int)>
    decreases end - pos,
{
    if pos < 0 || pos >= end {
        None
    } else {
        match vec16(b, pos + 2, end) {
            None => None,
            Some((s, e)) => if be16(b, pos) == g as nat {
                Some((s, e))
            } else {
                find_share(b, e, end, g)
            },
        }
    }
}

/// The first group of `groups[i..]` the client sent a key share for, and
/// that share.
pub open spec fn pick_share(b: Seq<u8>, s: int, e: int, groups: Seq<u16>, i: int) -> Option<
    (u16, (int, int)),
>
    decreases groups.len() - i,
{
    if i < 0 || i >= groups.len() {
        None
    } else {
        match find_share(b, s, e, groups[i]) {
            Some(sp) => Some((groups[i], sp)),
            None => pick_share(b, s, e, groups, i + 1),
        }
    }
}

/// The first ALPN protocol name in `[pos, end)` equal to `name`.
pub open spec fn alpn_has(b: Seq<u8>, pos: int, end: int, name: Seq<u8>) -> Option<(int, int)>
    decreases end - pos,
{
    if pos < 0 || pos >= end {
        None
    } else {
        match vec8(b, pos, end) {
            None => None,
            Some((s, e)) => if b.subrange(s, e) == name {
                Some((s, e))
            } else {
                alpn_has(b, e, end, name)
            },
        }
    }
}

/// The first of the server's protocols, `cfg[p..cend]` in ALPN wire form,
/// that the client offers in `b[cs..ce]` (RFC 7301 §3.2: "the server
/// SHALL select the most highly preferred protocol that it supports and
/// that is also advertised by the client"): its span in `cfg` and in `b`.
pub open spec fn pick_alpn(cfg: Seq<u8>, p: int, cend: int, b: Seq<u8>, cs: int, ce: int) -> Option<
    ((int, int), (int, int)),
>
    decreases cend - p,
{
    if p < 0 || p >= cend {
        None
    } else {
        match vec8(cfg, p, cend) {
            None => None,
            Some((s, e)) => match alpn_has(b, cs, ce, cfg.subrange(s, e)) {
                Some(c) => Some(((s, e), c)),
                None => pick_alpn(cfg, e, cend, b, cs, ce),
            },
        }
    }
}

/// What the server chose for a full handshake.
pub struct SpecChoice {
    pub suite: u16,
    pub group: u16,
    /// The client's key_exchange for `group`.
    pub share: (int, int),
    pub signature_scheme: u16,
    /// The protocol, as a span of the server's list and of the
    /// ClientHello, if the client offered ALPN.
    pub alpn: Option<((int, int), (int, int))>,
}

/// Alerts negotiation can end in (§6.2).
pub enum SpecNegAlert {
    /// `protocol_version` (70): the client does not offer TLS 1.3.
    ProtocolVersion,
    /// `illegal_parameter` (47).
    IllegalParameter,
    /// `missing_extension` (109), §9.2.
    MissingExtension,
    /// `handshake_failure` (40): no cipher suite, signature scheme or
    /// group in common.
    HandshakeFailure,
    /// `no_application_protocol` (120), RFC 7301 §3.2.
    NoApplicationProtocol,
}

pub enum SpecOutcome {
    /// A ServerHello can be sent.
    Accept(SpecChoice),
    /// No key share for a group the server takes, but a group in
    /// common: a HelloRetryRequest for `group` (§4.1.4).
    Retry { suite: u16, group: u16 },
    Reject(SpecNegAlert),
}

/// A TLS 1.3 server's choices for a full (certificate) handshake, from a
/// parsed ClientHello `h` of body `b`, given its preferences in order:
/// cipher suites, groups, signature schemes, and ALPN protocols in wire
/// form (`protocol_name_list`'s contents; empty for none). In order:
///
/// 1. supported_versions must offer TLS 1.3 (§4.2.1: a server "MUST NOT
///    use the ClientHello.legacy_version value for version negotiation"
///    when it is present), else `protocol_version`. This crate is TLS 1.3
///    only, so a ClientHello without it is `protocol_version` too.
/// 2. legacy_compression_methods must be exactly `[0]` (§4.1.2), else
///    `illegal_parameter`.
/// 3. signature_algorithms, supported_groups and key_share must be there
///    (§9.2, for a handshake not using PSK), else `missing_extension`.
/// 4. The first server cipher suite the client offers, the first server
///    signature scheme in signature_algorithms; none is
///    `handshake_failure`.
/// 5. If the client offered ALPN, the first server protocol it offers;
///    none is `no_application_protocol`.
/// 6. The first server group the client sent a key share for: Accept.
///    Otherwise the first server group in supported_groups: Retry.
///    Otherwise `handshake_failure` (§4.2.8, §4.1.1).
///
/// PSKs are not negotiated here: a server that does not resume just
/// ignores pre_shared_key (§4.2.11), which this does.
pub open spec fn negotiate(
    b: Seq<u8>,
    h: SpecHello,
    suites: Seq<u16>,
    groups: Seq<u16>,
    sigs: Seq<u16>,
    alpn: Seq<u8>,
) -> SpecOutcome {
    let (ms, me) = h.outer.compression_methods;
    let (cs, ce) = h.outer.cipher_suites;
    match h.supported_versions {
        None => SpecOutcome::Reject(SpecNegAlert::ProtocolVersion),
        Some((vs, ve)) => if !u16s(b, vs, ve).contains(TLS13) {
            SpecOutcome::Reject(SpecNegAlert::ProtocolVersion)
        } else if !(me - ms == 1 && b[ms] == 0) {
            SpecOutcome::Reject(SpecNegAlert::IllegalParameter)
        } else {
            match (h.signature_algorithms, h.supported_groups, h.key_shares) {
                (Some((ss, se)), Some((gs, ge)), Some((ks, ke))) => match (
                    first_in(suites, 0, u16s(b, cs, ce)),
                    first_in(sigs, 0, u16s(b, ss, se)),
                ) {
                    (Some(suite), Some(sig)) => {
                        let a = match h.alpn {
                            None => Some(None),
                            Some((as_, ae)) => match pick_alpn(
                                alpn,
                                0,
                                alpn.len() as int,
                                b,
                                as_,
                                ae,
                            ) {
                                Some(x) => Some(Some(x)),
                                None => None,
                            },
                        };
                        match a {
                            None => SpecOutcome::Reject(SpecNegAlert::NoApplicationProtocol),
                            Some(a) => match pick_share(b, ks, ke, groups, 0) {
                                Some((g, sp)) => SpecOutcome::Accept(
                                    SpecChoice {
                                        suite,
                                        group: g,
                                        share: sp,
                                        signature_scheme: sig,
                                        alpn: a,
                                    },
                                ),
                                None => match first_in(groups, 0, u16s(b, gs, ge)) {
                                    Some(g) => SpecOutcome::Retry { suite, group: g },
                                    None => SpecOutcome::Reject(SpecNegAlert::HandshakeFailure),
                                },
                            },
                        }
                    },
                    _ => SpecOutcome::Reject(SpecNegAlert::HandshakeFailure),
                },
                _ => SpecOutcome::Reject(SpecNegAlert::MissingExtension),
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Server names (RFC 6066 §3)
// ---------------------------------------------------------------------------

/// A letter, digit, hyphen or underscore. The underscore is not LDH
/// (RFC 1123), but names with one are common and rustls takes them.
pub open spec fn host_char(c: u8) -> bool {
    (0x30 <= c <= 0x39) || (0x41 <= c <= 0x5a) || (0x61 <= c <= 0x7a) || c == 0x2d || c == 0x5f
}

pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// One label `h[s..e]`: 1 to 63 bytes, not starting or ending in a hyphen.
pub open spec fn label_ok(h: Seq<u8>, s: int, e: int) -> bool {
    1 <= e - s <= 63 && h[s] != 0x2d && h[e - 1] != 0x2d
}

pub open spec fn all_digits(h: Seq<u8>, s: int, e: int) -> bool {
    forall|k: int| s <= k < e ==> is_digit(#[trigger] h[k])
}

/// The labels of `h` from `i`, the current one starting at `start`.
pub open spec fn labels_ok(h: Seq<u8>, i: int, start: int) -> bool
    decreases h.len() - i,
{
    if i < 0 || i >= h.len() {
        i == h.len() && label_ok(h, start, i) && !all_digits(h, start, i)
    } else if h[i] == 0x2e {
        label_ok(h, start, i) && labels_ok(h, i + 1, i + 1)
    } else {
        host_char(h[i]) && labels_ok(h, i + 1, start)
    }
}

/// A host name a server can match against its certificates: what RFC 6066
/// §3 allows in HostName ("the fully qualified DNS hostname", "without a
/// trailing dot", "Literal IPv4 and IPv6 addresses are not permitted"):
/// at most 253 bytes of labels of letters, digits, hyphens and
/// underscores, separated by dots, the last not all digits (which would
/// be an IPv4 address; an IPv6 one has colons). Case is not changed: DNS
/// names compare without case.
pub open spec fn valid_host_name(h: Seq<u8>) -> bool {
    1 <= h.len() <= 253 && labels_ok(h, 0, 0)
}

} // verus!
