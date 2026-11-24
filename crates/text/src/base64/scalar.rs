//! The scalar codec: proven to write `spec::encode` and to compute
//! `spec::decode`. The AVX2 kernels handle the bulk of long inputs and hand
//! their position to these loops, which finish the job.
use super::spec::*;
use super::tables::*;
use verilith_core::prims::{get, set};
use vstd::prelude::*;

verus! {

/// The length of the encoding of `n` bytes.
///
/// ```text
/// requires n <= usize::MAX / 2
/// ensures  r == encoded_len(n as nat, pad)
/// ```
pub fn enc_len(n: usize, pad: bool) -> (r: usize)
    requires
        n <= usize::MAX / 2,
    ensures
        r == encoded_len(n as nat, pad),
{
    if pad {
        4 * ((n + 2) / 3)
    } else {
        let r = n % 3;
        4 * (n / 3) + if r == 0 {
            0
        } else {
            r + 1
        }
    }
}

#[inline(always)]
fn enc_tab(url: bool) -> (r: &'static [u8; 64])
    ensures
        forall|x: u8| x < 64 ==> #[trigger] r@[x as int] == sym(url, x),
{
    proof {
        lemma_tables();
    }
    if url {
        &ENC_URL
    } else {
        &ENC_STD
    }
}

/// The decoding table of the alphabet: each byte's 6-bit value, or 255 for a byte outside it.
///
/// ```text
/// ensures  forall|c: u8| #[trigger] r@[c as int] == dec_entry(url, c)
/// ```
#[inline(always)]
pub fn dec_tab(url: bool) -> (r: &'static [u8; 256])
    ensures
        forall|c: u8| #[trigger] r@[c as int] == dec_entry(url, c),
{
    proof {
        lemma_tables();
    }
    if url {
        &DEC_URL
    } else {
        &DEC_STD
    }
}

/// Writes the characters of full groups `g0..x.len() / 3` into `out`.
/// `out[..4 * g0]` must already hold the characters before them.
pub fn encode_groups(url: bool, x: &[u8], out: &mut [u8], g0: usize)
    requires
        x.len() <= usize::MAX / 2,
        old(out).len() >= 4 * (x.len() / 3),
        g0 <= x.len() / 3,
    ensures
        final(out).len() == old(out).len(),
        forall|i: int| 4 * g0 <= i < 4 * (x.len() / 3) ==> #[trigger] final(out)@[i] == enc_char(url, x@, i),
        forall|i: int| 0 <= i < 4 * g0 ==> #[trigger] final(out)@[i] == old(out)@[i],
        forall|i: int| 4 * (x.len() / 3) <= i < final(out).len() ==> #[trigger] final(out)@[i] == old(out)@[i],
{
    let tab = enc_tab(url);
    let full = x.len() / 3;
    let mut g = g0;
    while g < full
        invariant
            forall|x: u8| x < 64 ==> #[trigger] tab@[x as int] == sym(url, x),
            full == x.len() / 3,
            x.len() <= usize::MAX / 2,
            g0 <= g <= full,
            out.len() == old(out).len(),
            old(out).len() >= 4 * full,
            forall|i: int| 4 * g0 <= i < 4 * g ==> #[trigger] out@[i] == enc_char(url, x@, i),
            forall|i: int| 0 <= i < 4 * g0 ==> #[trigger] out@[i] == old(out)@[i],
            forall|i: int| 4 * g <= i < out.len() ==> #[trigger] out@[i] == old(out)@[i],
        decreases full - g,
    {
        let a = get(x, 3 * g);
        let b = get(x, 3 * g + 1);
        let c = get(x, 3 * g + 2);
        proof {
            assert(a >> 2 < 64) by (bit_vector);
            assert(((a & 3) << 4) | (b >> 4) < 64) by (bit_vector);
            assert(((b & 15) << 2) | (c >> 6) < 64) by (bit_vector);
            assert(c & 63 < 64) by (bit_vector);
        }
        let o = 4 * g;
        set(out, o, tab[(a >> 2) as usize]);
        set(out, o + 1, tab[(((a & 3) << 4) | (b >> 4)) as usize]);
        set(out, o + 2, tab[(((b & 15) << 2) | (c >> 6)) as usize]);
        set(out, o + 3, tab[(c & 63) as usize]);
        proof {
            assert forall|t: int| 0 <= t < 4 implies #[trigger] out@[4 * g + t] == enc_char(url, x@, 4 * g + t) by {
                lemma_group_index(g as int, t);
            }
            assert forall|i: int| 4 * g0 <= i < 4 * (g + 1) implies #[trigger] out@[i] == enc_char(url, x@, i) by {
                if i >= 4 * g {
                    assert(out@[4 * g + (i - 4 * g)] == enc_char(url, x@, 4 * g + (i - 4 * g)));
                }
            }
        }
        g = g + 1;
    }
}

/// Writes `encode(cfg, x)` into `out`, whose length must be the encoded
/// length.
pub fn encode_into(cfg: Config, x: &[u8], out: &mut [u8])
    requires
        x.len() <= usize::MAX / 2,
        old(out).len() == encoded_len(x.len() as nat, cfg.pad),
    ensures
        final(out)@ == encode(cfg, x@),
{
    let g = if verilith_simd::cpu::has_avx2() {
        // The CPU has AVX2.
        super::avx2::encode_bulk(cfg.url, x, out)
    } else {
        0
    };
    encode_groups(cfg.url, x, out, g);
    encode_tail(cfg, x, out);
}

/// Writes the final partial group and the padding, given the full groups.
pub fn encode_tail(cfg: Config, x: &[u8], out: &mut [u8])
    requires
        x.len() <= usize::MAX / 2,
        old(out).len() == encoded_len(x.len() as nat, cfg.pad),
        forall|i: int| 0 <= i < 4 * (x.len() / 3) ==> #[trigger] old(out)@[i] == enc_char(cfg.url, x@, i),
    ensures
        final(out)@ == encode(cfg, x@),
{
    let ghost e = encode(cfg, x@);
    let tab = enc_tab(cfg.url);
    let n = x.len();
    let full = n / 3;
    let o = 4 * full;
    let r = n - 3 * full;
    if r == 1 {
        let a = get(x, 3 * full);
        proof {
            assert(a >> 2 < 64) by (bit_vector);
            assert(((a & 3) << 4) | (0u8 >> 4) < 64) by (bit_vector);
            assert(((a & 3) << 4) | (0u8 >> 4) == (a & 3) << 4) by (bit_vector);
        }
        set(out, o, tab[(a >> 2) as usize]);
        set(out, o + 1, tab[((a & 3) << 4) as usize]);
        if cfg.pad {
            set(out, o + 2, PAD);
            set(out, o + 3, PAD);
        }
        proof {
            lemma_group_index(full as int, 0);
            lemma_group_index(full as int, 1);
        }
    } else if r == 2 {
        let a = get(x, 3 * full);
        let b = get(x, 3 * full + 1);
        proof {
            assert(a >> 2 < 64) by (bit_vector);
            assert(((a & 3) << 4) | (b >> 4) < 64) by (bit_vector);
            assert(((b & 15) << 2) | (0u8 >> 6) < 64) by (bit_vector);
            assert(((b & 15) << 2) | (0u8 >> 6) == (b & 15) << 2) by (bit_vector);
        }
        set(out, o, tab[(a >> 2) as usize]);
        set(out, o + 1, tab[(((a & 3) << 4) | (b >> 4)) as usize]);
        set(out, o + 2, tab[((b & 15) << 2) as usize]);
        if cfg.pad {
            set(out, o + 3, PAD);
        }
        proof {
            lemma_group_index(full as int, 0);
            lemma_group_index(full as int, 1);
            lemma_group_index(full as int, 2);
        }
    }
    assert(out@ =~= e);
}

/// The number of `=` at the end of `s`.
pub fn pad_count_exec(s: &[u8]) -> (r: usize)
    ensures
        r == pad_count(s@),
{
    let n = s.len();
    if n >= 2 && s[n - 1] == PAD && s[n - 2] == PAD {
        2
    } else if n >= 1 && s[n - 1] == PAD {
        1
    } else {
        0
    }
}

/// The number of characters of `s` before its padding.
///
/// ```text
/// ensures  r == body_len(cfg, s@)
/// ```
pub fn body_len_exec(cfg: Config, s: &[u8]) -> (r: usize)
    ensures
        r == body_len(cfg, s@),
{
    if cfg.pad {
        s.len() - pad_count_exec(s)
    } else {
        s.len()
    }
}

/// The number of bytes `m` data characters decode to.
///
/// ```text
/// ensures  r == decoded_len(m as nat)
///          r <= m
/// ```
pub fn dec_len(m: usize) -> (r: usize)
    ensures
        r == decoded_len(m as nat),
        r <= m,
{
    let q = m / 4;
    let r = m % 4;
    3 * q + if r == 0 {
        0
    } else {
        r - 1
    }
}

/// The "everything so far was valid" test on an OR of table entries:
/// valid entries are below 64, invalid ones are 255.
pub open spec fn ok_acc(acc: u8) -> bool {
    acc & 0x80 == 0
}

proof fn lemma_acc_or(acc: u8, e: u8)
    requires
        e < 64 || e == 255,
    ensures
        ok_acc(acc | e) <==> ok_acc(acc) && e < 64,
{
    assert(e < 64 || e == 255 ==> (((acc | e) & 0x80 == 0) <==> (acc & 0x80 == 0 && e < 64))) by (bit_vector);
}

/// Decodes the full groups `g0..m / 4` of the body `s[..m]` into `out`,
/// assuming `out[..3 * g0]` holds the bytes before them. Returns `false` if
/// one of their characters is not in the alphabet (the output is then
/// unspecified); otherwise `true`, with the bytes written.
pub fn decode_groups(url: bool, s: &[u8], m: usize, out: &mut [u8], g0: usize) -> (ok: bool)
    requires
        m <= s.len(),
        old(out).len() >= 3 * (m / 4),
        g0 <= m / 4,
    ensures
        final(out).len() == old(out).len(),
        ok <==> forall|j: int| 4 * g0 <= j < 4 * (m / 4) ==> (#[trigger] val(url, s@[j])) is Some,
        ok ==> forall|i: int| 3 * g0 <= i < 3 * (m / 4) ==> #[trigger] final(out)@[i] == dec_byte(url, s@, m as int, i),
        forall|i: int| 0 <= i < 3 * g0 ==> #[trigger] final(out)@[i] == old(out)@[i],
        forall|i: int| 3 * (m / 4) <= i < final(out).len() ==> #[trigger] final(out)@[i] == old(out)@[i],
{
    let tab = dec_tab(url);
    let full = m / 4;
    let mut g = g0;
    let mut acc: u8 = 0;
    assert(0u8 & 0x80 == 0) by (bit_vector);
    while g < full
        invariant
            forall|c: u8| #[trigger] tab@[c as int] == dec_entry(url, c),
            full == m / 4,
            m <= s.len(),
            g0 <= g <= full,
            out.len() == old(out).len(),
            old(out).len() >= 3 * full,
            ok_acc(acc) <==> forall|j: int| 4 * g0 <= j < 4 * g ==> (#[trigger] val(url, s@[j])) is Some,
            ok_acc(acc) ==> forall|i: int| 3 * g0 <= i < 3 * g ==> #[trigger] out@[i] == dec_byte(url, s@, m as int, i),
            forall|i: int| 0 <= i < 3 * g0 ==> #[trigger] out@[i] == old(out)@[i],
            forall|i: int| 3 * g <= i < out.len() ==> #[trigger] out@[i] == old(out)@[i],
        decreases full - g,
    {
        let j = 4 * g;
        let p = tab[get(s, j) as usize];
        let q = tab[get(s, j + 1) as usize];
        let r = tab[get(s, j + 2) as usize];
        let w = tab[get(s, j + 3) as usize];
        let ghost acc0 = acc;
        acc = acc | p | q | r | w;
        proof {
            lemma_acc_or(acc0, p);
            lemma_acc_or(acc0 | p, q);
            lemma_acc_or(acc0 | p | q, r);
            lemma_acc_or(acc0 | p | q | r, w);
            assert(ok_acc(acc) <==> ok_acc(acc0) && p < 64 && q < 64 && r < 64 && w < 64);
        }
        let o = 3 * g;
        set(out, o, (p << 2) | (q >> 4));
        set(out, o + 1, (q << 4) | (r >> 2));
        set(out, o + 2, (r << 6) | w);
        proof {
            assert(ok_acc(acc) <==> forall|j2: int| 4 * g0 <= j2 < 4 * (g + 1) ==> (#[trigger] val(url, s@[j2])) is Some) by {
                if ok_acc(acc) {
                    assert forall|j2: int| 4 * g0 <= j2 < 4 * (g + 1) implies (#[trigger] val(url, s@[j2])) is Some by {
                        if j2 >= j {
                            assert(val(url, s@[j + (j2 - j)]) is Some);
                        }
                    }
                }
                if forall|j2: int| 4 * g0 <= j2 < 4 * (g + 1) ==> (#[trigger] val(url, s@[j2])) is Some {
                    assert(val(url, s@[j + 0]) is Some);
                    assert(val(url, s@[j + 1]) is Some);
                    assert(val(url, s@[j + 2]) is Some);
                    assert(val(url, s@[j + 3]) is Some);
                }
            }
            if ok_acc(acc) {
                assert(4 * g + 3 < m) by {
                    assert(g + 1 <= m / 4);
                }
                assert(p == vb(url, s@, m as int, 4 * g));
                assert(q == vb(url, s@, m as int, 4 * g + 1));
                assert(r == vb(url, s@, m as int, 4 * g + 2));
                assert(w == vb(url, s@, m as int, 4 * g + 3));
                assert forall|t: int| 0 <= t < 3 implies #[trigger] out@[3 * g + t] == dec_byte(url, s@, m as int, 3 * g + t) by {
                    lemma_byte_index(g as int, t);
                }
                assert forall|i: int| 3 * g0 <= i < 3 * (g + 1) implies #[trigger] out@[i] == dec_byte(url, s@, m as int, i) by {
                    if i >= 3 * g {
                        assert(out@[3 * g + (i - 3 * g)] == dec_byte(url, s@, m as int, 3 * g + (i - 3 * g)));
                    }
                }
            }
        }
        g = g + 1;
    }
    ok_acc_exec(acc)
}

#[inline(always)]
fn ok_acc_exec(acc: u8) -> (r: bool)
    ensures
        r == ok_acc(acc),
{
    acc & 0x80 == 0
}

/// Checks the length and padding of `s`, and decodes its final partial
/// group, given that the full groups decoded with all characters valid.
/// Returns whether `s` is decodable.
pub fn decode_tail(cfg: Config, s: &[u8], m: usize, out: &mut [u8]) -> (ok: bool)
    requires
        m == body_len(cfg, s@),
        old(out).len() == decoded_len(m as nat),
        forall|j: int| 0 <= j < 4 * (m / 4) ==> (#[trigger] val(cfg.url, s@[j])) is Some,
        forall|i: int| 0 <= i < 3 * (m / 4) ==> #[trigger] old(out)@[i] == dec_byte(cfg.url, s@, m as int, i),
    ensures
        ok == decodable(cfg, s@),
        ok ==> final(out)@ == decode(cfg, s@)->0,
{
    let tab = dec_tab(cfg.url);
    let rem = m % 4;
    if rem == 1 {
        return false;
    }
    if cfg.pad && s.len() % 4 != 0 {
        return false;
    }
    let full = m / 4;
    let j = 4 * full;
    let o = 3 * full;
    proof {
        assert(j + rem == m);
        assert(o + (if rem == 0 { 0 } else { rem - 1 }) == out.len());
    }
    if rem == 0 {
        assert(out@ =~= decode(cfg, s@)->0);
        return true;
    }
    let p = tab[get(s, j) as usize];
    let q = tab[get(s, j + 1) as usize];
    if rem == 2 {
        if p >= 64 || q >= 64 || q & 15 != 0 {
            proof {
                if decodable(cfg, s@) {
                    assert(val(cfg.url, s@[j as int]) is Some);
                    assert(val(cfg.url, s@[j + 1]) is Some);
                }
            }
            return false;
        }
        set(out, o, (p << 2) | (q >> 4));
        proof {
            assert forall|jj: int| 0 <= jj < m implies (#[trigger] val(cfg.url, s@[jj])) is Some by {
                if jj >= j {
                    assert(jj == j || jj == j + 1);
                }
            }
            lemma_byte_index(full as int, 0);
            assert(out@[o as int] == dec_byte(cfg.url, s@, m as int, o as int));
            assert(out@ =~= decode(cfg, s@)->0);
        }
        return true;
    }
    let r = tab[get(s, j + 2) as usize];
    if p >= 64 || q >= 64 || r >= 64 || r & 3 != 0 {
        proof {
            if decodable(cfg, s@) {
                assert(val(cfg.url, s@[j as int]) is Some);
                assert(val(cfg.url, s@[j + 1]) is Some);
                assert(val(cfg.url, s@[j + 2]) is Some);
            }
        }
        return false;
    }
    set(out, o, (p << 2) | (q >> 4));
    set(out, o + 1, (q << 4) | (r >> 2));
    proof {
        assert forall|jj: int| 0 <= jj < m implies (#[trigger] val(cfg.url, s@[jj])) is Some by {
            if jj >= j {
                assert(jj == j || jj == j + 1 || jj == j + 2);
            }
        }
        lemma_byte_index(full as int, 0);
        lemma_byte_index(full as int, 1);
        assert(out@[o as int] == dec_byte(cfg.url, s@, m as int, o as int));
        assert(out@[o + 1] == dec_byte(cfg.url, s@, m as int, o + 1));
        assert(out@ =~= decode(cfg, s@)->0);
    }
    true
}

/// Decodes `s` into `out`, whose length must be `decoded_len` of the body.
/// Returns whether `s` is a canonical encoding; if so, `out` holds
/// `decode(cfg, s)`.
pub fn decode_into(cfg: Config, s: &[u8], out: &mut [u8]) -> (ok: bool)
    requires
        old(out).len() == decoded_len(body_len(cfg, s@)),
    ensures
        ok == decode(cfg, s@) is Some,
        ok ==> final(out)@ == decode(cfg, s@)->0,
{
    let m = body_len_exec(cfg, s);
    proof {
        assert(3 * (m / 4) <= decoded_len(m as nat));
    }
    let (g, ok) = if verilith_simd::cpu::has_avx2() {
        // The CPU has AVX2.
        super::avx2::decode_bulk(cfg.url, s, m, out)
    } else {
        (0, true)
    };
    if !ok {
        proof {
            assert(!decodable(cfg, s@)) by {
                if decodable(cfg, s@) {
                    assert forall|k: int| 0 <= k < 4 * g implies (#[trigger] val(cfg.url, s@[k])) is Some by {
                        assert(k < m);
                    }
                }
            }
        }
        return false;
    }
    if !decode_groups(cfg.url, s, m, out, g) {
        return false;
    }
    proof {
        assert forall|j: int| 0 <= j < 4 * (m / 4) implies (#[trigger] val(cfg.url, s@[j])) is Some by {
            if j < 4 * g {
            }
        }
    }
    decode_tail(cfg, s, m, out)
}

} // verus!
