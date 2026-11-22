//! The uniqueness theorem for chunked bodies: a chunked body vhttp's
//! decoder accepts ends at the same byte, and decodes to the same bytes,
//! under every chunk reader in `rfc.rs`, including the lenient ones behind
//! the 2023-2025 chunk-extension and "funky chunks" smuggling attacks.
use crate::chunked::*;
use crate::rfc::*;
use crate::spec::*;
use crate::unique::*;
use vstd::prelude::*;

verus! {

/// `b` from `j` on.
pub open spec fn sfx(b: Seq<u8>, j: int) -> Seq<u8> {
    b.subrange(j, b.len() as int)
}

/// The state after a size line declaring `n` bytes.
pub open spec fn after_size(n: nat) -> CState {
    if n == 0 {
        CState::TrStart
    } else {
        CState::Data { left: n as u64 }
    }
}

/// The states inside a size line after the chunk size, and the size they
/// carry.
pub open spec fn ext_n(s: CState) -> Option<u64> {
    match s {
        CState::SizeWs { n } => Some(n),
        CState::ExtPreName { n } => Some(n),
        CState::ExtName { n } => Some(n),
        CState::ExtNameWs { n } => Some(n),
        CState::ExtPreVal { n } => Some(n),
        CState::ExtTok { n } => Some(n),
        CState::ExtQ { n } => Some(n),
        CState::ExtQEsc { n } => Some(n),
        CState::ExtValEnd { n } => Some(n),
        CState::ExtValWs { n } => Some(n),
        _ => None,
    }
}

pub open spec fn done(r: Option<(CState, Seq<u8>, nat)>) -> bool {
    r matches Some((s, _, _)) && s is Done
}

/// One step of `run` at `b[j]`.
proof fn lemma_step(s: CState, b: Seq<u8>, j: int)
    requires
        0 <= j < b.len(),
        !(s is Done),
    ensures
        run(s, sfx(b, j), false) == match step(s, b[j]) {
            None => None,
            Some((s2, emit)) => then(
                if emit {
                    seq![b[j]]
                } else {
                    Seq::empty()
                },
                1,
                run(s2, sfx(b, j + 1), false),
            ),
        },
{
    assert(sfx(b, j)[0] == b[j]);
    assert(sfx(b, j).drop_first() =~= sfx(b, j + 1));
}

/// `run` never reaches `Done` from a state other than `Done` on no input.
proof fn lemma_end(s: CState, b: Seq<u8>)
    requires
        done(run(s, sfx(b, b.len() as int), false)),
    ensures
        s is Done,
{
    assert(sfx(b, b.len() as int).len() == 0);
}

proof fn lemma_then(o1: Seq<u8>, k1: nat, o2: Seq<u8>, k2: nat, r: Option<(CState, Seq<u8>, nat)>)
    ensures
        then(o1, k1, then(o2, k2, r)) == then(o1 + o2, k1 + k2, r),
{
    if let Some((s, o, k)) = r {
        assert(o1 + (o2 + o) =~= (o1 + o2) + o);
    }
}

proof fn lemma_find_crlf(b: Seq<u8>, i: int, e: int)
    requires
        0 <= i <= e,
        e + 1 < b.len(),
        b[e] == CR,
        b[e + 1] == LF,
        clean(b, i, e),
    ensures
        find_crlf(b, i) == e,
    decreases e - i,
{
    if i < e {
        lemma_find_crlf(b, i + 1, e);
    }
}

/// The CR LF ending a size line: after the chunk size, a size line reads
/// to the first CR, which LF follows, and then the data or trailers start.
proof fn lemma_ext(s: CState, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        ext_n(s) is Some,
        done(run(s, sfx(b, j), false)),
    ensures
        ({
            let e = find(b, j, CR);
            &&& j <= e
            &&& e + 1 < b.len()
            &&& b[e] == CR
            &&& b[e + 1] == LF
            &&& clean(b, j, e)
            &&& run(s, sfx(b, j), false) == then(
                Seq::empty(),
                (e + 2 - j) as nat,
                run(after_size(ext_n(s)->0 as nat), sfx(b, e + 2), false),
            )
        }),
    decreases b.len() - j,
{
    if j == b.len() {
        lemma_end(s, b);
    }
    let n = ext_n(s)->0;
    lemma_step(s, b, j);
    match step(s, b[j]) {
        None => {},
        Some((s2, emit)) => {
            assert(!emit);
            if s2 is SizeLf {
                assert(b[j] == CR);
                assert(s2 == CState::SizeLf { n });
                if j + 1 == b.len() {
                    lemma_end(s2, b);
                }
                lemma_step(s2, b, j + 1);
                assert(b[j + 1] == LF);
                assert(step(s2, b[j + 1]) == Some((after_size(n as nat), false)));
                lemma_then(Seq::empty(), 1, Seq::empty(), 1, run(after_size(n as nat), sfx(b, j + 2), false));
                assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
            } else {
                assert(ext_n(s2) == Some(n));
                assert(b[j] != CR && b[j] != LF);
                lemma_ext(s2, b, j + 1);
                let e = find(b, j + 1, CR);
                lemma_then(Seq::empty(), 1, Seq::empty(), (e + 2 - (j + 1)) as nat, run(after_size(n as nat), sfx(b, e + 2), false));
                assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
            }
        },
    }
}

/// Whitespace after the chunk size is followed by `;`.
proof fn lemma_size_ws(n: u64, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        done(run(CState::SizeWs { n }, sfx(b, j), false)),
    ensures
        ({
            let r = ltrim(b.subrange(j, find(b, j, CR)));
            r.len() > 0 && r[0] == 0x3B
        }),
    decreases b.len() - j,
{
    let s = CState::SizeWs { n };
    lemma_ext(s, b, j);
    let e = find(b, j, CR);
    lemma_step(s, b, j);
    let t = b.subrange(j, e);
    if is_ows(b[j]) {
        lemma_size_ws(n, b, j + 1);
        assert(t[0] == b[j]);
        assert(t.drop_first() =~= b.subrange(j + 1, e));
    } else {
        assert(b[j] == 0x3B);
        assert(t[0] == b[j]);
        lemma_ltrim(t, 0);
        assert(t.subrange(0, t.len() as int) =~= t);
    }
}

proof fn lemma_hex_value_digit(s: Seq<u8>, c: u8)
    requires
        is_hex(c),
    ensures
        hex_value(s.push(c)) == hex_value(s) * 16 + hex_val(c) as nat,
        hexdig(c),
{
    assert(s.push(c).drop_last() =~= s);
}

/// The chunk size: `b[i..p]` are hex digits worth `n`, and the decoder is
/// in `Size { n }` at `p`.
proof fn lemma_digits(b: Seq<u8>, i: int, p: int, n: u64)
    requires
        0 <= i < p <= b.len(),
        forall|k: int| i <= k < p ==> is_hex(#[trigger] b[k]),
        n as nat == hex_value(b.subrange(i, p)),
        done(run(CState::Size { n }, sfx(b, p), false)),
    ensures
        ({
            let e = find(b, p, CR);
            let q = hex_end(b, p);
            let v = hex_value(b.subrange(i, q));
            let r = ltrim(b.subrange(q, e));
            &&& p <= q <= e
            &&& e + 1 < b.len()
            &&& b[e] == CR
            &&& b[e + 1] == LF
            &&& clean(b, i, e)
            &&& forall|k: int| i <= k < q ==> hexdig(#[trigger] b[k])
            &&& v <= u64::MAX
            &&& (r.len() == 0 || r[0] == 0x3B)
            &&& run(CState::Size { n }, sfx(b, p), false) == then(
                Seq::empty(),
                (e + 2 - p) as nat,
                run(after_size(v), sfx(b, e + 2), false),
            )
        }),
    decreases b.len() - p,
{
    let s = CState::Size { n };
    if p == b.len() {
        lemma_end(s, b);
    }
    lemma_step(s, b, p);
    assert forall|k: int| i <= k < p implies #[trigger] b[k] != LF && b[k] != CR && hexdig(b[k]) by {
        assert(is_hex(b[k]));
    }
    if is_hex(b[p]) {
        assert(n <= MAX_BEFORE_DIGIT);
        let n2 = (n * 16 + hex_val(b[p])) as u64;
        assert(n * 16 + hex_val(b[p]) <= u64::MAX) by (nonlinear_arith)
            requires
                n <= 0x0fff_ffff_ffff_ffff,
                hex_val(b[p]) <= 15,
        ;
        lemma_hex_value_digit(b.subrange(i, p), b[p]);
        assert(b.subrange(i, p).push(b[p]) =~= b.subrange(i, p + 1));
        lemma_digits(b, i, p + 1, n2);
        let e = find(b, p + 1, CR);
        lemma_then(Seq::empty(), 1, Seq::empty(), (e + 2 - (p + 1)) as nat, run(after_size(hex_value(b.subrange(i, hex_end(b, p + 1)))), sfx(b, e + 2), false));
        assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
    } else {
        assert(hex_end(b, p) == p);
        assert(b.subrange(i, p) == b.subrange(i, hex_end(b, p)));
        if b[p] == CR {
            assert(find(b, p, CR) == p);
            let s2 = CState::SizeLf { n };
            if p + 1 == b.len() {
                lemma_end(s2, b);
            }
            lemma_step(s2, b, p + 1);
            assert(b[p + 1] == LF);
            assert(step(s2, b[p + 1]) == Some((after_size(n as nat), false)));
            lemma_then(Seq::empty(), 1, Seq::empty(), 1, run(after_size(n as nat), sfx(b, p + 2), false));
            assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
            assert(b.subrange(p, p).len() == 0);
        } else {
            let s2 = if is_ows(b[p]) {
                CState::SizeWs { n }
            } else {
                CState::ExtPreName { n }
            };
            assert(step(s, b[p]) == Some((s2, false)));
            lemma_ext(s2, b, p + 1);
            let e = find(b, p + 1, CR);
            assert(find(b, p, CR) == e);
            lemma_then(Seq::empty(), 1, Seq::empty(), (e + 2 - (p + 1)) as nat, run(after_size(n as nat), sfx(b, e + 2), false));
            assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
            let t = b.subrange(p, e);
            assert(t[0] == b[p]);
            if is_ows(b[p]) {
                lemma_size_ws(n, b, p + 1);
                assert(t.drop_first() =~= b.subrange(p + 1, e));
            } else {
                assert(b[p] == 0x3B);
                lemma_ltrim(t, 0);
                assert(t.subrange(0, t.len() as int) =~= t);
            }
        }
    }
}

/// `hex_end` on a line `b[i..e]` is `hex_end` on `b`, when `b[e]` ends
/// the digits.
proof fn lemma_hex_end_sub(b: Seq<u8>, i: int, e: int, k: int)
    requires
        0 <= i <= e < b.len(),
        !hexdig(b[e]),
        0 <= k <= e - i,
    ensures
        hex_end(b.subrange(i, e), k) == hex_end(b, i + k) - i,
    decreases e - i - k,
{
    let l = b.subrange(i, e);
    if k < e - i {
        assert(l[k] == b[i + k]);
        lemma_hex_end_sub(b, i, e, k + 1);
    }
}

/// A trailer line: from inside its name or value, it reads to the first
/// CR, which LF follows.
proof fn lemma_trailer_line(s: CState, b: Seq<u8>, j: int)
    requires
        0 <= j <= b.len(),
        s is TrName || s is TrValue,
        done(run(s, sfx(b, j), false)),
    ensures
        ({
            let e = find(b, j, CR);
            &&& j <= e
            &&& e + 1 < b.len()
            &&& b[e] == CR
            &&& b[e + 1] == LF
            &&& clean(b, j, e)
            &&& run(s, sfx(b, j), false) == then(
                Seq::empty(),
                (e + 2 - j) as nat,
                run(CState::TrStart, sfx(b, e + 2), false),
            )
        }),
    decreases b.len() - j,
{
    if j == b.len() {
        lemma_end(s, b);
    }
    lemma_step(s, b, j);
    match step(s, b[j]) {
        None => {},
        Some((s2, emit)) => {
            assert(!emit);
            if s2 is TrLf {
                assert(b[j] == CR);
                if j + 1 == b.len() {
                    lemma_end(s2, b);
                }
                lemma_step(s2, b, j + 1);
                assert(b[j + 1] == LF);
                lemma_then(Seq::empty(), 1, Seq::empty(), 1, run(CState::TrStart, sfx(b, j + 2), false));
                assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
            } else {
                assert(s2 is TrName || s2 is TrValue);
                assert(b[j] != CR && b[j] != LF);
                lemma_trailer_line(s2, b, j + 1);
                let e = find(b, j + 1, CR);
                lemma_then(Seq::empty(), 1, Seq::empty(), (e + 2 - (j + 1)) as nat, run(CState::TrStart, sfx(b, e + 2), false));
                assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
            }
        },
    }
}

/// The trailer section: every recipient reads it as lines up to an empty
/// one, ending where the decoder stops, with no body bytes.
proof fn lemma_trailers(b: Seq<u8>, j: int, c: Recipient)
    requires
        0 <= j <= b.len(),
        done(run(CState::TrStart, sfx(b, j), false)),
    ensures
        run(CState::TrStart, sfx(b, j), false)->Some_0.1.len() == 0,
        read_lines(b, j, c) matches Parsed::Done(_, e) && e == j + run(
            CState::TrStart,
            sfx(b, j),
            false,
        )->Some_0.2,
    decreases b.len() - j,
{
    let s = CState::TrStart;
    if j == b.len() {
        lemma_end(s, b);
    }
    lemma_step(s, b, j);
    if b[j] == CR {
        let s2 = CState::EndLf;
        if j + 1 == b.len() {
            lemma_end(s2, b);
        }
        lemma_step(s2, b, j + 1);
        assert(b[j + 1] == LF);
        assert(run(CState::Done, sfx(b, j + 2), false) == Some((CState::Done, Seq::<u8>::empty(), 0nat)));
        lemma_read_clean(b, j, j, c);
        assert(b.subrange(j, j).len() == 0);
    } else {
        assert(is_tchar(b[j]));
        lemma_trailer_line(CState::TrName, b, j + 1);
        let e = find(b, j + 1, CR);
        assert(find(b, j, CR) == e);
        lemma_then(Seq::empty(), 1, Seq::empty(), (e + 2 - (j + 1)) as nat, run(CState::TrStart, sfx(b, e + 2), false));
        assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
        lemma_trailers(b, e + 2, c);
        let o = run(CState::TrStart, sfx(b, e + 2), false)->Some_0.1;
        assert(Seq::<u8>::empty() + o =~= o);
        lemma_read_clean(b, j, e, c);
        assert(b.subrange(j, e)[0] == b[j]);
    }
}

/// A size line: every reader reads it to the CR LF the decoder stops at,
/// and finds the same chunk size.
proof fn lemma_size_line(b: Seq<u8>, i: int, c: ChunkReader)
    requires
        0 <= i <= b.len(),
        done(run(CState::SizeStart, sfx(b, i), false)),
    ensures
        ({
            let e = find(b, i, CR);
            let v = hex_value(b.subrange(i, hex_end(b, i)));
            &&& i < e
            &&& e + 2 <= b.len()
            &&& v <= u64::MAX
            &&& read_size_line(b, i, c) == Parsed::Done(b.subrange(i, e), e + 2)
            &&& chunk_size(b.subrange(i, e), c) == Some(v)
            &&& run(CState::SizeStart, sfx(b, i), false) == then(
                Seq::empty(),
                (e + 2 - i) as nat,
                run(after_size(v), sfx(b, e + 2), false),
            )
        }),
{
    let s = CState::SizeStart;
    if i == b.len() {
        lemma_end(s, b);
    }
    lemma_step(s, b, i);
    assert(is_hex(b[i]));
    let n0 = hex_val(b[i]);
    lemma_hex_value_digit(Seq::empty(), b[i]);
    assert(Seq::<u8>::empty().push(b[i]) =~= b.subrange(i, i + 1));
    assert(hex_value(Seq::<u8>::empty()) == 0);
    lemma_digits(b, i, i + 1, n0);
    let e = find(b, i + 1, CR);
    assert(find(b, i, CR) == e);
    let q = hex_end(b, i + 1);
    assert(hex_end(b, i) == q);
    let v = hex_value(b.subrange(i, q));
    lemma_then(
        Seq::empty(),
        1,
        Seq::empty(),
        (e + 2 - (i + 1)) as nat,
        run(after_size(v), sfx(b, e + 2), false),
    );
    assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
    let l = b.subrange(i, e);
    lemma_find_crlf(b, i, e);
    lemma_read_clean(b, i, e, c.line);
    assert(l[0] == b[i]);
    lemma_ltrim(l, 0);
    assert(l.subrange(0, l.len() as int) =~= l);
    lemma_hex_end_sub(b, i, e, 0);
    assert(l.subrange(q - i, l.len() as int) =~= b.subrange(q, e));
    assert(l.subrange(0, q - i) =~= b.subrange(i, q));
}

/// Chunk data of `v > 0` bytes at `n`: the decoder emits `b[n..n+v]`,
/// then needs CR LF, and every reader's data end agrees.
proof fn lemma_data(b: Seq<u8>, n: int, v: nat, c: ChunkReader)
    requires
        0 <= n <= b.len(),
        0 < v <= u64::MAX,
        done(run(after_size(v), sfx(b, n), false)),
    ensures
        n + v + 2 <= b.len(),
        data_end(b, n + v, c) == Parsed::Done((), n + v + 2),
        run(after_size(v), sfx(b, n), false) == then(
            b.subrange(n, n + v),
            v + 2,
            run(CState::SizeStart, sfx(b, n + v + 2), false),
        ),
{
    let d = n + v;
    let sb = sfx(b, n);
    if d > b.len() {
        if sb.len() == 0 {
            assert(sb =~= sfx(b, b.len() as int));
            lemma_end(after_size(v), b);
        } else {
            lemma_run_data(v as u64, sb, sb.len(), false);
            assert(sb.subrange(sb.len() as int, sb.len() as int).len() == 0);
        }
    } else {
        lemma_run_data(v as u64, sb, v, false);
        assert(sb.subrange(v as int, sb.len() as int) =~= sfx(b, d));
        assert(sb.subrange(0, v as int) =~= b.subrange(n, d));
        if d == b.len() {
            lemma_end(CState::DataCr, b);
        }
        lemma_step(CState::DataCr, b, d);
        assert(b[d] == CR);
        if d + 1 == b.len() {
            lemma_end(CState::DataLf, b);
        }
        lemma_step(CState::DataLf, b, d + 1);
        assert(b[d + 1] == LF);
        lemma_read_clean(b, d, d, c.line);
        assert(b.subrange(d, d).len() == 0);
        let r = run(CState::SizeStart, sfx(b, d + 2), false);
        lemma_then(Seq::empty(), 1, Seq::empty(), 1, r);
        lemma_then(b.subrange(n, d), v, Seq::empty(), 2, r);
        assert(Seq::<u8>::empty() + Seq::empty() =~= Seq::<u8>::empty());
        assert(b.subrange(n, d) + Seq::empty() =~= b.subrange(n, d));
    }
}

/// Every chunk reader reads the chunked body at `i` as the decoder does.
proof fn lemma_chunks(b: Seq<u8>, i: int, c: ChunkReader)
    requires
        0 <= i <= b.len(),
        done(run(CState::SizeStart, sfx(b, i), false)),
    ensures
        ({
            let (_, o, k) = run(CState::SizeStart, sfx(b, i), false)->Some_0;
            read_chunks(b, i, c) == ChunkReading::Done { end: i + k, body: o }
        }),
    decreases b.len() - i,
{
    lemma_size_line(b, i, c);
    let e = find(b, i, CR);
    let v = hex_value(b.subrange(i, hex_end(b, i)));
    let n = e + 2;
    let r = run(after_size(v), sfx(b, n), false);
    if v == 0 {
        lemma_trailers(b, n, c.line);
        let o = r->Some_0.1;
        assert(Seq::<u8>::empty() + o =~= Seq::<u8>::empty());
    } else {
        lemma_data(b, n, v, c);
        let d = n + v;
        lemma_chunks(b, d + 2, c);
        let o2 = run(CState::SizeStart, sfx(b, d + 2), false)->Some_0.1;
        lemma_then(Seq::empty(), (n - i) as nat, b.subrange(n, d), v + 2, run(CState::SizeStart, sfx(b, d + 2), false));
        assert(Seq::<u8>::empty() + b.subrange(n, d) =~= b.subrange(n, d));
    }
}

/// **Chunked-body uniqueness.** If vhttp's decoder accepts `b` as a
/// complete chunked body, ending at `k` and decoding to `out`, then every
/// chunk reader in the model, strict or lenient, reads the body as ending
/// at `k` and decoding to `out`. With the head theorems in `unique.rs`,
/// this covers the whole message: no reader in the model sees a
/// different next message after a message vhttp accepts.
pub proof fn theorem_chunked_unique(b: Seq<u8>, c: ChunkReader)
    requires
        done(run(CState::SizeStart, b, false)),
    ensures
        ({
            let (_, out, k) = run(CState::SizeStart, b, false)->Some_0;
            read_chunks(b, 0, c) == ChunkReading::Done { end: k as int, body: out }
        }),
{
    assert(sfx(b, 0) =~= b);
    lemma_chunks(b, 0, c);
}

} // verus!
