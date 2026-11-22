//! Base64 (RFC 4648 §4 and §5) as spec functions: the encoding, and a
//! decoding that accepts exactly the canonical encodings.
//!
//! Both alphabets and both padding modes are covered. `encode` is the RFC's
//! encoding. `decode` is defined structurally, the way an implementation
//! reads its input, and `lemma_decode_iff_encode` proves that it returns
//! `Some(x)` exactly when `encode(x)` is the input: so a decoder proven to
//! compute `decode` rejects every non-canonical string (bad characters,
//! wrong padding, nonzero trailing bits) and nothing else.
use vstd::prelude::*;

verus! {

/// One configuration: the alphabet (`url`: `-_` for values 62 and 63,
/// otherwise `+/`) and whether the output is padded with `=` to a multiple
/// of four. These are the base64 crate's `STANDARD`, `STANDARD_NO_PAD`,
/// `URL_SAFE` and `URL_SAFE_NO_PAD`.
#[derive(Clone, Copy)]
pub struct Config {
    pub url: bool,
    pub pad: bool,
}

pub const PAD: u8 = 0x3D;  // '='

/// The character for a 6-bit value (Table 1 and Table 2 of RFC 4648).
pub open spec fn sym(url: bool, v: u8) -> u8 {
    if v < 26 {
        (v + 65) as u8  // 'A'..
    } else if v < 52 {
        (v + 71) as u8  // 'a'..
    } else if v < 62 {
        (v - 4) as u8  // '0'..
    } else if v == 62 {
        if url { 0x2D } else { 0x2B }  // '-' or '+'

    } else {
        if url { 0x5F } else { 0x2F }  // '_' or '/'

    }
}

/// The value of a character, if it is in the alphabet.
pub open spec fn val(url: bool, c: u8) -> Option<u8> {
    if 65 <= c <= 90 {
        Some((c - 65) as u8)
    } else if 97 <= c <= 122 {
        Some((c - 71) as u8)
    } else if 48 <= c <= 57 {
        Some((c + 4) as u8)
    } else if c == (if url { 0x2Du8 } else { 0x2Bu8 }) {
        Some(62)
    } else if c == (if url { 0x5Fu8 } else { 0x2Fu8 }) {
        Some(63)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

/// The 6-bit value of output character `t` (0..4) of the group `a b c`.
pub open spec fn sext(a: u8, b: u8, c: u8, t: int) -> u8 {
    if t == 0 {
        a >> 2
    } else if t == 1 {
        ((a & 3) << 4) | (b >> 4)
    } else if t == 2 {
        ((b & 15) << 2) | (c >> 6)
    } else {
        c & 63
    }
}

/// Byte `i` of `x`, or 0 past its end (the zero bits RFC 4648 appends to a
/// final partial group).
pub open spec fn at(x: Seq<u8>, i: int) -> u8 {
    if 0 <= i < x.len() {
        x[i]
    } else {
        0
    }
}

/// Character `i` of the encoding of `x`, ignoring padding.
pub open spec fn enc_char(url: bool, x: Seq<u8>, i: int) -> u8 {
    let g = i / 4;
    sym(url, sext(at(x, 3 * g), at(x, 3 * g + 1), at(x, 3 * g + 2), i % 4))
}

/// Number of characters before padding: 4 per full group, then 2 or 3.
pub open spec fn unpadded_len(n: nat) -> nat {
    4 * (n / 3) + if n % 3 == 0 {
        0
    } else {
        n % 3 + 1
    }
}

pub open spec fn encoded_len(n: nat, pad: bool) -> nat {
    if pad {
        4 * ((n + 2) / 3)
    } else {
        unpadded_len(n)
    }
}

/// The base64 encoding of `x`.
pub open spec fn encode(cfg: Config, x: Seq<u8>) -> Seq<u8> {
    let u = unpadded_len(x.len());
    Seq::new(encoded_len(x.len(), cfg.pad), |i: int| if i < u { enc_char(cfg.url, x, i) } else { PAD })
}

// ---------------------------------------------------------------------------
// Decoding
// ---------------------------------------------------------------------------

/// The number of `=` at the end of `s`: 2, 1 or 0.
pub open spec fn pad_count(s: Seq<u8>) -> nat {
    let n = s.len();
    if n >= 2 && s[n - 1] == PAD && s[n - 2] == PAD {
        2
    } else if n >= 1 && s[n - 1] == PAD {
        1
    } else {
        0
    }
}

/// The characters that carry data: all of `s`, less its padding in padded
/// mode.
pub open spec fn body_len(cfg: Config, s: Seq<u8>) -> nat {
    if cfg.pad {
        (s.len() - pad_count(s)) as nat
    } else {
        s.len()
    }
}

/// The value of character `j` (only used where it is in the alphabet).
pub open spec fn v(url: bool, s: Seq<u8>, j: int) -> u8 {
    match val(url, s[j]) {
        Some(x) => x,
        None => 0,
    }
}

/// The value of character `j`, or 0 past `m` (the end of the body).
pub open spec fn vb(url: bool, s: Seq<u8>, m: int, j: int) -> u8 {
    if j < m {
        v(url, s, j)
    } else {
        0
    }
}

/// Byte `t` (0..3) of the group with values `p q r w`.
pub open spec fn dbyte(p: u8, q: u8, r: u8, w: u8, t: int) -> u8 {
    if t == 0 {
        (p << 2) | (q >> 4)
    } else if t == 1 {
        (q << 4) | (r >> 2)
    } else {
        (r << 6) | w
    }
}

/// Byte `i` of the decoding of the body `s[..m]`.
pub open spec fn dec_byte(url: bool, s: Seq<u8>, m: int, i: int) -> u8 {
    let g = i / 3;
    dbyte(vb(url, s, m, 4 * g), vb(url, s, m, 4 * g + 1), vb(url, s, m, 4 * g + 2), vb(url, s, m, 4 * g + 3), i % 3)
}

/// The body length `m` is one an encoding can have, the padding matches it,
/// every body character is in the alphabet, and the bits a final partial
/// group drops are zero.
pub open spec fn decodable(cfg: Config, s: Seq<u8>) -> bool {
    let m = body_len(cfg, s);
    &&& m % 4 != 1
    &&& cfg.pad ==> s.len() % 4 == 0
    &&& forall|j: int| 0 <= j < m ==> (#[trigger] val(cfg.url, s[j])) is Some
    &&& m % 4 == 2 ==> v(cfg.url, s, m - 1) & 15 == 0
    &&& m % 4 == 3 ==> v(cfg.url, s, m - 1) & 3 == 0
}

/// Bytes decoded from a body of `m` characters.
pub open spec fn decoded_len(m: nat) -> nat {
    3 * (m / 4) + if m % 4 == 0 {
        0
    } else {
        (m % 4 - 1) as nat
    }
}

/// The decoding of `s`, or `None` if it is not a canonical encoding.
pub open spec fn decode(cfg: Config, s: Seq<u8>) -> Option<Seq<u8>> {
    let m = body_len(cfg, s);
    if decodable(cfg, s) {
        Some(Seq::new(decoded_len(m), |i: int| dec_byte(cfg.url, s, m as int, i)))
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

pub proof fn lemma_val_sym(url: bool, x: u8)
    requires
        x < 64,
    ensures
        val(url, sym(url, x)) == Some(x),
{
}

pub proof fn lemma_sym_val(url: bool, c: u8)
    requires
        val(url, c) is Some,
    ensures
        sym(url, val(url, c)->0) == c,
        val(url, c)->0 < 64,
{
}

pub proof fn lemma_sext_small(a: u8, b: u8, c: u8)
    ensures
        a >> 2 < 64,
        ((a & 3) << 4) | (b >> 4) < 64,
        ((b & 15) << 2) | (c >> 6) < 64,
        c & 63 < 64,
{
    assert(a >> 2 < 64) by (bit_vector);
    assert(((a & 3) << 4) | (b >> 4) < 64) by (bit_vector);
    assert(((b & 15) << 2) | (c >> 6) < 64) by (bit_vector);
    assert(c & 63 < 64) by (bit_vector);
}

/// Decoding the four values of an encoded group gives the group back.
proof fn lemma_group_roundtrip(a: u8, b: u8, c: u8)
    ensures
        dbyte(sext(a, b, c, 0), sext(a, b, c, 1), sext(a, b, c, 2), sext(a, b, c, 3), 0) == a,
        dbyte(sext(a, b, c, 0), sext(a, b, c, 1), sext(a, b, c, 2), sext(a, b, c, 3), 1) == b,
        dbyte(sext(a, b, c, 0), sext(a, b, c, 1), sext(a, b, c, 2), sext(a, b, c, 3), 2) == c,
{
    assert(((a >> 2) << 2) | ((((a & 3) << 4) | (b >> 4)) >> 4) == a) by (bit_vector);
    assert(((((a & 3) << 4) | (b >> 4)) << 4) | ((((b & 15) << 2) | (c >> 6)) >> 2) == b)
        by (bit_vector);
    assert(((((b & 15) << 2) | (c >> 6)) << 6) | (c & 63) == c) by (bit_vector);
}

/// Encoding the bytes decoded from four values gives the values back.
proof fn lemma_group_canonical(p: u8, q: u8, r: u8, w: u8)
    requires
        p < 64,
        q < 64,
        r < 64,
        w < 64,
    ensures
        ({
            let a = dbyte(p, q, r, w, 0);
            let b = dbyte(p, q, r, w, 1);
            let c = dbyte(p, q, r, w, 2);
            sext(a, b, c, 0) == p && sext(a, b, c, 1) == q && sext(a, b, c, 2) == r && sext(
                a,
                b,
                c,
                3,
            ) == w
        }),
{
    assert(p < 64 && q < 64 ==> ((p << 2) | (q >> 4)) >> 2 == p) by (bit_vector);
    assert(p < 64 && q < 64 && r < 64 ==> ((((p << 2) | (q >> 4)) & 3) << 4) | (((q << 4) | (r
        >> 2)) >> 4) == q) by (bit_vector);
    assert(q < 64 && r < 64 && w < 64 ==> ((((q << 4) | (r >> 2)) & 15) << 2) | (((r << 6) | w)
        >> 6) == r) by (bit_vector);
    assert(r < 64 && w < 64 ==> ((r << 6) | w) & 63 == w) by (bit_vector);
}

pub proof fn lemma_group_index(g: int, t: int)
    requires
        g >= 0,
        0 <= t < 4,
    ensures
        (4 * g + t) / 4 == g,
        (4 * g + t) % 4 == t,
{
    assert((4 * g + t) / 4 == g && (4 * g + t) % 4 == t) by (nonlinear_arith)
        requires
            g >= 0,
            0 <= t < 4,
    ;
}

pub proof fn lemma_byte_index(g: int, t: int)
    requires
        g >= 0,
        0 <= t < 3,
    ensures
        (3 * g + t) / 3 == g,
        (3 * g + t) % 3 == t,
{
    assert((3 * g + t) / 3 == g && (3 * g + t) % 3 == t) by (nonlinear_arith)
        requires
            g >= 0,
            0 <= t < 3,
    ;
}

/// Each character of the body of an encoding is in the alphabet, is not
/// `=`, and has the value `sext` gives.
proof fn lemma_enc_char(url: bool, x: Seq<u8>, i: int)
    requires
        i >= 0,
    ensures
        val(url, enc_char(url, x, i)) == Some(sext(at(x, 3 * (i / 4)), at(x, 3 * (i / 4) + 1), at(x, 3 * (i / 4) + 2), i % 4)),
        enc_char(url, x, i) != PAD,
{
    let g = i / 4;
    lemma_sext_small(at(x, 3 * g), at(x, 3 * g + 1), at(x, 3 * g + 2));
    lemma_val_sym(url, sext(at(x, 3 * g), at(x, 3 * g + 1), at(x, 3 * g + 2), i % 4));
}

/// The body of an encoding is its unpadded part.
proof fn lemma_enc_body(cfg: Config, x: Seq<u8>)
    ensures
        body_len(cfg, encode(cfg, x)) == unpadded_len(x.len()),
{
    let s = encode(cfg, x);
    let n = x.len();
    let u = unpadded_len(n) as int;
    if cfg.pad {
        assert(n == 3 * (n / 3) + n % 3);
        if u > 0 {
            lemma_enc_char(cfg.url, x, u - 1);
            assert(s[u - 1] != PAD);
        }
        if n % 3 == 1 {
            assert(s.len() == u + 2);
            assert(s[u] == PAD && s[u + 1] == PAD);
        } else if n % 3 == 2 {
            assert(s.len() == u + 1);
            assert(s[u] == PAD);
            lemma_enc_char(cfg.url, x, u - 2);
        } else {
            assert(s.len() == u);
        }
    }
}

/// The value of body character `4 * g + t` of an encoding, or 0 past the
/// body, is `sext` of group `g` of the zero-filled input.
proof fn lemma_enc_vb(cfg: Config, x: Seq<u8>, g: int, t: int)
    requires
        0 <= g,
        3 * g < x.len(),
        0 <= t < 4,
    ensures
        vb(cfg.url, encode(cfg, x), unpadded_len(x.len()) as int, 4 * g + t) == sext(at(x, 3 * g), at(x, 3 * g + 1), at(x, 3 * g + 2), t),
{
    let s = encode(cfg, x);
    let n = x.len() as int;
    let m = unpadded_len(x.len()) as int;
    assert(n == 3 * (n / 3) + n % 3);
    let a = at(x, 3 * g);
    let b = at(x, 3 * g + 1);
    let c = at(x, 3 * g + 2);
    if 4 * g + t < m {
        lemma_enc_char(cfg.url, x, 4 * g + t);
        lemma_group_index(g, t);
    } else {
        // Past the body: the last group is partial and `t` reads only
        // bytes past the end.
        if g < n / 3 {
            assert(4 * g + t < 4 * (n / 3)) by (nonlinear_arith)
                requires
                    g < n / 3,
                    t < 4,
            ;
        }
        assert(g == n / 3);
        if n % 3 == 1 {
            assert(b == 0 && c == 0);
            assert(t >= 2);
            assert(((0u8 & 15) << 2) | (0u8 >> 6) == 0) by (bit_vector);
            assert(0u8 & 63 == 0) by (bit_vector);
        } else {
            assert(n % 3 == 2);
            assert(t == 3 && c == 0);
            assert(0u8 & 63 == 0) by (bit_vector);
        }
    }
}

/// The round trip: decoding an encoding gives the input back.
pub proof fn lemma_decode_encode(cfg: Config, x: Seq<u8>)
    ensures
        decode(cfg, encode(cfg, x)) == Some(x),
{
    let s = encode(cfg, x);
    let n = x.len() as int;
    let m = unpadded_len(x.len()) as int;
    assert(n == 3 * (n / 3) + n % 3);
    lemma_enc_body(cfg, x);
    assert forall|j: int| 0 <= j < m implies (#[trigger] val(cfg.url, s[j])) is Some by {
        lemma_enc_char(cfg.url, x, j);
    }
    // Trailing bits are zero: the missing bytes read as 0.
    if m % 4 == 2 {
        let g = (m - 1) / 4;
        assert(m - 1 == 4 * g + 1);
        lemma_enc_char(cfg.url, x, m - 1);
        lemma_group_index(g, 1);
        assert(at(x, 3 * g + 1) == 0);
        let a = at(x, 3 * g);
        assert((((a & 3) << 4) | (0u8 >> 4)) & 15 == 0) by (bit_vector);
    }
    if m % 4 == 3 {
        let g = (m - 1) / 4;
        assert(m - 1 == 4 * g + 2);
        lemma_enc_char(cfg.url, x, m - 1);
        lemma_group_index(g, 2);
        assert(at(x, 3 * g + 2) == 0);
        let b = at(x, 3 * g + 1);
        assert((((b & 15) << 2) | (0u8 >> 6)) & 3 == 0) by (bit_vector);
    }
    assert(decodable(cfg, s));
    let d = decode(cfg, s)->0;
    assert(d.len() == n);
    assert forall|i: int| 0 <= i < n implies d[i] == x[i] by {
        let g = i / 3;
        let a = at(x, 3 * g);
        let b = at(x, 3 * g + 1);
        let c = at(x, 3 * g + 2);
        lemma_group_roundtrip(a, b, c);
        lemma_enc_vb(cfg, x, g, 0);
        lemma_enc_vb(cfg, x, g, 1);
        lemma_enc_vb(cfg, x, g, 2);
        lemma_enc_vb(cfg, x, g, 3);
        assert(i == 3 * g + i % 3);
    }
    assert(d =~= x);
}

/// How the decoded length relates to the body length.
proof fn lemma_dec_len(m: int)
    requires
        m >= 0,
        m % 4 != 1,
    ensures
        decoded_len(m as nat) / 3 == m / 4,
        decoded_len(m as nat) % 3 == if m % 4 == 0 { 0 } else { m % 4 - 1 },
        unpadded_len(decoded_len(m as nat)) == m,
{
    let q = m / 4;
    let r = if m % 4 == 0 { 0 } else { m % 4 - 1 };
    assert(decoded_len(m as nat) == 3 * q + r);
    lemma_byte_index(q, r);
}

/// Byte `3 * g + k` of the decoding, read with `at`, is `dbyte` of group
/// `g`'s values: past the end, the zero trailing bits make it 0.
proof fn lemma_dec_at(cfg: Config, s: Seq<u8>, g: int, k: int)
    requires
        decode(cfg, s) is Some,
        0 <= g,
        4 * g < body_len(cfg, s),
        0 <= k < 3,
    ensures
        ({
            let m = body_len(cfg, s) as int;
            at(decode(cfg, s)->0, 3 * g + k) == dbyte(vb(cfg.url, s, m, 4 * g), vb(cfg.url, s, m, 4 * g + 1), vb(cfg.url, s, m, 4 * g + 2), vb(cfg.url, s, m, 4 * g + 3), k)
        }),
{
    let m = body_len(cfg, s) as int;
    let x = decode(cfg, s)->0;
    let n = x.len() as int;
    lemma_dec_len(m);
    assert(n == 3 * (n / 3) + n % 3);
    assert(m == 4 * (m / 4) + m % 4);
    let p = vb(cfg.url, s, m, 4 * g);
    let q = vb(cfg.url, s, m, 4 * g + 1);
    let r = vb(cfg.url, s, m, 4 * g + 2);
    let w = vb(cfg.url, s, m, 4 * g + 3);
    if 3 * g + k < n {
        lemma_byte_index(g, k);
    } else {
        if g < m / 4 {
            assert(3 * g + k < 3 * (m / 4)) by (nonlinear_arith)
                requires
                    g < m / 4,
                    k < 3,
            ;
        }
        assert(g == m / 4);
        lemma_sym_val(cfg.url, s[4 * g]);
        if m % 4 == 2 {
            lemma_sym_val(cfg.url, s[4 * g + 1]);
            assert(q & 15 == 0);
            assert(q < 64 && q & 15 == 0 ==> (q << 4) | (0u8 >> 2) == 0) by (bit_vector);
            assert((0u8 << 6) | 0u8 == 0) by (bit_vector);
        } else {
            assert(m % 4 == 3);
            assert(k == 2);
            lemma_sym_val(cfg.url, s[4 * g + 2]);
            assert(r & 3 == 0);
            assert(r < 64 && r & 3 == 0 ==> (r << 6) | 0u8 == 0) by (bit_vector);
        }
    }
}

/// Canonicity: whatever `decode` accepts is the encoding of its result.
pub proof fn lemma_encode_decode(cfg: Config, s: Seq<u8>)
    requires
        decode(cfg, s) is Some,
    ensures
        encode(cfg, decode(cfg, s)->0) == s,
{
    let m = body_len(cfg, s) as int;
    let x = decode(cfg, s)->0;
    let e = encode(cfg, x);
    lemma_dec_len(m);
    assert(encoded_len(x.len(), cfg.pad) == s.len()) by {
        if cfg.pad {
            assert(pad_count(s) <= 2);
            assert(m == 4 * (m / 4) + m % 4);
        }
    }
    assert forall|i: int| 0 <= i < s.len() implies e[i] == s[i] by {
        if i < m {
            let g = i / 4;
            let p = vb(cfg.url, s, m, 4 * g);
            let q = vb(cfg.url, s, m, 4 * g + 1);
            let r = vb(cfg.url, s, m, 4 * g + 2);
            let w = vb(cfg.url, s, m, 4 * g + 3);
            assert forall|t: int| 0 <= t < 4 implies #[trigger] vb(cfg.url, s, m, 4 * g + t) < 64 by {
                if 4 * g + t < m {
                    lemma_sym_val(cfg.url, s[4 * g + t]);
                }
            }
            assert(p < 64 && q < 64 && r < 64 && w < 64) by {
                assert(vb(cfg.url, s, m, 4 * g + 0) < 64);
            }
            lemma_group_canonical(p, q, r, w);
            lemma_dec_at(cfg, s, g, 0);
            lemma_dec_at(cfg, s, g, 1);
            lemma_dec_at(cfg, s, g, 2);
            assert(i == 4 * g + i % 4);
            lemma_sym_val(cfg.url, s[i]);
        } else {
            // Padding.
            assert(cfg.pad);
            assert(s[i] == PAD);
        }
    }
    assert(e =~= s);
}

/// `decode` accepts exactly the encodings, and inverts them.
pub proof fn lemma_decode_iff_encode(cfg: Config, s: Seq<u8>, x: Seq<u8>)
    ensures
        decode(cfg, s) == Some(x) <==> encode(cfg, x) == s,
{
    if encode(cfg, x) == s {
        lemma_decode_encode(cfg, x);
    }
    if decode(cfg, s) == Some(x) {
        lemma_encode_decode(cfg, s);
    }
}

} // verus!
