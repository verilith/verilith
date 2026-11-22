//! Parallel compression: the input is cut into chunks, each chunk is
//! compressed on its own thread by a `Deflater` primed with the 32 KiB
//! before it, and the pieces are joined into one ordinary raw, zlib or gzip
//! stream that any decoder reads (the scheme pigz uses).
//!
//! The theorem (`compress`) is the serial compressor's: the output
//! decompresses, in its format, to exactly the input. Each piece is proven
//! by `Deflater::piece` to be blocks that add its chunk to the output
//! before it; `lemma_piece_join` joins two such pieces into one, and
//! `lemma_joined` closes the stream with a final empty block and the
//! trailer.
//!
//! The one function here that Verus does not check is `run`, which hands
//! the jobs to threads. It is safe Rust, and what it is trusted for is
//! that slot `k` of its result holds what the verified `job` returned for
//! `k`, or nothing. `compress` does any job a thread did not.
#[cfg(verus_only)]
use crate::bitwriter::*;
use crate::deflate::*;
use crate::dstream::*;
#[cfg(verus_only)]
use crate::slemmas::*;
#[cfg(verus_only)]
use crate::spec::*;
use crate::wrap::Format;
use vstd::prelude::*;

verus! {

/// The shortest chunk: a piece is primed with the 32 KiB before it, which
/// is then all a match can reach.
pub const MIN_CHUNK: usize = 32768;

/// The chunk `compress_auto` uses.
pub const CHUNK: usize = 262144;

/// Where chunk `i` ends.
pub open spec fn chunk_end(len: int, chunk: int, i: int) -> int {
    if (i + 1) * chunk < len {
        (i + 1) * chunk
    } else {
        len
    }
}

/// `v` closes a stream whose output so far is `all`: a final block that
/// adds nothing, then the trailer for `fmt` (RFC 1950 2.2, RFC 1952 2.3.1).
pub open spec fn end_ok(fmt: Format, all: Seq<u8>, v: Seq<u8>) -> bool {
    match inflate_blocks(v, 0, all) {
        Some((e, o)) => {
            let tail = v.subrange((e + 7) / 8, v.len() as int);
            &&& o == all
            &&& 0 <= e
            &&& (e + 7) / 8 + tail.len() == v.len()
            &&& fmt == Format::Raw ==> tail.len() == 0
            &&& fmt == Format::Zlib ==> tail.len() == 4 && be32(tail, 0) == adler32(all)
            &&& fmt == Format::Gzip ==> tail.len() == 8 && le32(tail, 0) == crc32(all) as nat && le32(tail, 4) == all.len()
                % 0x1_0000_0000
        },
        None => false,
    }
}

/// What job `k` must return. Job 0 closes the stream (it computes the
/// checksum, so it is handed out first); job `k >= 1` is the piece for
/// chunk `k - 1`, made after the 32 KiB before the chunk.
pub open spec fn job_ok(fmt: Format, data: Seq<u8>, chunk: int, k: int, v: Seq<u8>) -> bool {
    if k == 0 {
        end_ok(fmt, data, v)
    } else {
        let a = (k - 1) * chunk;
        let b = chunk_end(data.len() as int, chunk, k - 1);
        is_piece(
            v,
            if k == 1 {
                Seq::empty()
            } else {
                data.subrange(a - 32768, a)
            },
            data.subrange(a, b),
        )
    }
}

/// The final block and the trailer.
fn end_job(fmt: Format, data: &[u8]) -> (r: Vec<u8>)
    ensures
        end_ok(fmt, data@, r@),
{
    let mut tail: Vec<u8> = Vec::new();
    match fmt {
        Format::Raw => {},
        Format::Zlib => {
            let t = be_bytes(crate::checksum::adler32(data));
            tail.push(t[0]);
            tail.push(t[1]);
            tail.push(t[2]);
            tail.push(t[3]);
            proof {
                assert(tail@ =~= t@);
            }
        },
        Format::Gzip => {
            let c = le_bytes(crate::checksum::crc32(data));
            let l = le_bytes(((data.len() as u64) % 0x1_0000_0000) as u32);
            tail.push(c[0]);
            tail.push(c[1]);
            tail.push(c[2]);
            tail.push(c[3]);
            tail.push(l[0]);
            tail.push(l[1]);
            tail.push(l[2]);
            tail.push(l[3]);
            proof {
                assert(tail@.subrange(0, 4) =~= c@);
                assert(tail@.subrange(4, 8) =~= l@);
                assert(le32(tail@, 0) == le32(c@, 0));
                assert(le32(tail@, 4) == le32(l@, 0));
            }
        },
    }
    let empty: [u8; 0] = [];
    let mut enc = Encoder::with_header_base(&empty, 16, Ghost(data@));
    enc.stored(&empty, true);
    let r = enc.finish_tail(tail.as_slice());
    proof {
        assert(data@ + empty@ =~= data@);
        assert(Seq::<u8>::empty() + r@ =~= r@);
    }
    r
}

/// Job `k` of compressing `data` in chunks of `chunk` bytes.
pub fn job(fmt: Format, data: &[u8], level: u32, wbits: u32, chunk: usize, k: usize) -> (r: Vec<u8>)
    requires
        8 <= wbits <= 15,
        chunk >= MIN_CHUNK,
        k >= 1 ==> (k - 1) * chunk < data@.len(),
    ensures
        job_ok(fmt, data@, chunk as int, k as int, r@),
{
    if k == 0 {
        return end_job(fmt, data);
    }
    let n = data.len();
    let i = k - 1;
    proof {
        assert(i * chunk >= i) by (nonlinear_arith)
            requires
                chunk >= 1,
                i >= 0,
        ;
        if i >= 1 {
            assert(i * chunk >= chunk) by (nonlinear_arith)
                requires
                    chunk >= 1,
                    i >= 1,
            ;
        }
        assert((i + 1) * chunk == i * chunk + chunk) by (nonlinear_arith);
    }
    let a = i * chunk;
    let b = if n - a > chunk { a + chunk } else { n };
    let d = if i == 0 {
        Deflater::new_sized(Format::Raw, level, wbits, b - a)
    } else {
        Deflater::new_with_dict(Format::Raw, level, wbits, vstd::slice::slice_subrange(data, a - 32768, a))
    };
    d.piece(vstd::slice::slice_subrange(data, a, b))
}

/// Runs jobs `0..=n` on up to `threads` threads, this one included. Slot
/// `k` of the result is what `job` returned for `k`, or `None` if no
/// thread got to it (a thread could not be started, or died).
///
/// Trusted: Verus does not check this body. It is safe Rust with no
/// `unsafe`; the claim it is trusted for is the `ensures`, that a result
/// is stored in the slot of the job that made it.
#[verifier::external_body]
fn run(fmt: Format, data: &[u8], level: u32, wbits: u32, chunk: usize, n: usize, threads: usize) -> (r: Vec<Option<Vec<u8>>>)
    requires
        8 <= wbits <= 15,
        chunk >= MIN_CHUNK,
        n >= 1 ==> (n - 1) * chunk < data@.len(),
        n < usize::MAX,
    ensures
        r@.len() == n + 1,
        forall|k: int| 0 <= k <= n ==> (#[trigger] r@[k] matches Some(v) ==> job_ok(fmt, data@, chunk as int, k, v@)),
{
    let next = std::sync::atomic::AtomicUsize::new(0);
    let work = || {
        let mut done = Vec::new();
        loop {
            let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if k > n {
                return done;
            }
            done.push((k, job(fmt, data, level, wbits, chunk, k)));
        }
    };
    let mut r: Vec<Option<Vec<u8>>> = (0..=n).map(|_| None).collect();
    std::thread::scope(|s| {
        let spawned: Vec<_> = (1..threads.min(n + 1)).filter_map(|_| std::thread::Builder::new().spawn_scoped(s, &work).ok()).collect();
        let mut all = work();
        for h in spawned {
            all.extend(h.join().unwrap_or_default());
        }
        for (k, v) in all {
            r[k] = Some(v);
        }
    });
    r
}

/// No bytes are a piece that adds nothing.
proof fn lemma_piece_empty(p: Seq<u8>)
    ensures
        is_piece(Seq::empty(), p, Seq::empty()),
{
    hide(inflate_blocks);
    reveal(is_piece);
    assert(p + Seq::<u8>::empty() =~= p);
}

/// A piece made after the 32 KiB window `d` is a piece after any output
/// that ends with `d`.
proof fn lemma_piece_lift(s: Seq<u8>, pfx: Seq<u8>, d: Seq<u8>, c: Seq<u8>)
    requires
        is_piece(s, d, c),
        d.len() >= MAX_DIST,
    ensures
        is_piece(s, pfx + d, c),
{
    hide(inflate_blocks);
    reveal(is_piece);
    assert forall|t: Seq<u8>| #[trigger] inflate_blocks(s + t, 0, pfx + d) == inflate_blocks(s + t, 8 * s.len() as int, (pfx + d) + c) by {
        lemma_win_blocks(s + t, 0, pfx, d);
        lemma_win_blocks(s + t, 8 * s.len() as int, pfx, d + c);
        assert(inflate_blocks(s + t, 0, d) == inflate_blocks(s + t, 8 * s.len() as int, d + c));
        assert(pfx + (d + c) =~= (pfx + d) + c);
    }
}

/// Two pieces, the second made after the first's output, are one piece.
proof fn lemma_piece_join(s1: Seq<u8>, s2: Seq<u8>, p: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>)
    requires
        is_piece(s1, p, c1),
        is_piece(s2, p + c1, c2),
    ensures
        is_piece(s1 + s2, p, c1 + c2),
{
    hide(inflate_blocks);
    reveal(is_piece);
    let s = s1 + s2;
    assert forall|t: Seq<u8>| #[trigger] inflate_blocks(s + t, 0, p) == inflate_blocks(s + t, 8 * s.len() as int, p + (c1 + c2)) by {
        let b = s + t;
        let d = s1.len() as int;
        let x = (p + c1) + c2;
        assert(b =~= s1 + (s2 + t));
        assert(inflate_blocks(s1 + (s2 + t), 0, p) == inflate_blocks(s1 + (s2 + t), 8 * s1.len() as int, p + c1));
        assert(skip(b, d) =~= s2 + t);
        lemma_shift_blocks(b, d, 0, p + c1);
        assert(inflate_blocks(s2 + t, 0, p + c1) == inflate_blocks(s2 + t, 8 * s2.len() as int, x));
        lemma_shift_blocks(b, d, 8 * s2.len() as int, x);
        assert(8 * s2.len() as int + 8 * d == 8 * s.len() as int);
        let r1 = inflate_blocks(b, 8 * d, p + c1);
        let r2 = inflate_blocks(b, 8 * s.len() as int, x);
        assert(sh(r1, d) == sh(r2, d));
        assert(r1 == r2) by {
            match (r1, r2) {
                (Some((q1, o1)), Some((q2, o2))) => {
                    assert(q1 - 8 * d == q2 - 8 * d);
                },
                _ => {},
            }
        }
        assert(x =~= p + (c1 + c2));
    }
}

/// The joined stream: a header, pieces that together add `all` to an
/// empty output, and the closing bytes decompress to `all`.
proof fn lemma_joined(fmt: Format, head: Seq<u8>, j: Seq<u8>, e: Seq<u8>, all: Seq<u8>)
    requires
        head_ok(fmt, head),
        is_piece(j, Seq::empty(), all),
        end_ok(fmt, all, e),
    ensures
        crate::wrap::spec_decompress(fmt, head + j + e) == Some((all, (head + j + e).len() as int)),
{
    hide(inflate_blocks);
    reveal(is_piece);
    let t = head + j + e;
    let h = head.len() as int;
    let (q, o) = inflate_blocks(e, 0, all).unwrap();
    let tail = e.subrange((q + 7) / 8, e.len() as int);
    assert(skip(t, h) =~= j + e);
    lemma_shift_blocks(t, h, 0, Seq::empty());
    assert(inflate_blocks(j + e, 0, Seq::empty()) == inflate_blocks(j + e, 8 * j.len() as int, Seq::<u8>::empty() + all));
    assert(Seq::<u8>::empty() + all =~= all);
    assert(skip(j + e, j.len() as int) =~= e);
    lemma_shift_blocks(j + e, j.len() as int, 0, all);
    let r1 = inflate_blocks(j + e, 8 * j.len() as int, all);
    assert(sh(r1, j.len() as int) == Some((q, all)));
    assert(r1 == Some((q + 8 * j.len() as int, all)));
    let r0 = inflate_blocks(t, 8 * h, Seq::empty());
    assert(sh(r0, h) == r1);
    let q0 = q + 8 * j.len() as int + 8 * h;
    assert(r0 == Some((q0, all)));
    assert((q0 + 7) / 8 == (q + 7) / 8 + j.len() + h);
    assert(t.subrange((q0 + 7) / 8, t.len() as int) =~= tail);
    assert(t.subrange(0, h) =~= head);
    lemma_finish(fmt, t, head, tail, all);
}

/// How many chunks of `chunk` bytes `len` bytes make.
fn chunks(len: usize, chunk: usize) -> (n: usize)
    requires
        chunk >= 1,
    ensures
        n >= 1 ==> (n - 1) * chunk < len,
        n * chunk >= len,
        n <= len,
{
    proof {
        let q = len as int / chunk as int;
        let m = len as int % chunk as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(len as int, chunk as int);
        assert(len == chunk * q + m);
        assert(chunk * q == q * chunk) by (nonlinear_arith);
        assert((q + 1) * chunk == q * chunk + chunk) by (nonlinear_arith);
        assert((q - 1) * chunk == q * chunk - chunk) by (nonlinear_arith);
        assert(q * chunk >= q) by (nonlinear_arith)
            requires
                q >= 0,
                chunk >= 1,
        ;
    }
    let n = if len % chunk == 0 { len / chunk } else { len / chunk + 1 };
    n
}

/// Piece `i` joins the pieces before it.
proof fn lemma_step(fmt: Format, data: Seq<u8>, chunk: int, i: int, j: Seq<u8>, v: Seq<u8>)
    requires
        chunk >= MIN_CHUNK,
        0 <= i,
        i * chunk < data.len(),
        is_piece(j, Seq::empty(), data.subrange(0, chunk_end(data.len() as int, chunk, i - 1))),
        job_ok(fmt, data, chunk, i + 1, v),
    ensures
        is_piece(j + v, Seq::empty(), data.subrange(0, chunk_end(data.len() as int, chunk, i))),
{
    let a = i * chunk;
    let b = chunk_end(data.len() as int, chunk, i);
    assert((i - 1 + 1) * chunk == i * chunk) by (nonlinear_arith);
    assert((i + 1) * chunk == i * chunk + chunk) by (nonlinear_arith);
    assert(chunk_end(data.len() as int, chunk, i - 1) == a);
    assert(i + 1 - 1 == i);
    let p = data.subrange(0, a);
    let c = data.subrange(a, b);
    if i == 0 {
        assert(a == 0);
        assert(p =~= Seq::<u8>::empty());
        assert(is_piece(v, Seq::empty(), c));
    } else {
        assert(i * chunk >= chunk) by (nonlinear_arith)
            requires
                i >= 1,
                chunk >= 0,
        ;
        let d = data.subrange(a - 32768, a);
        assert(is_piece(v, d, c));
        lemma_piece_lift(v, data.subrange(0, a - 32768), d, c);
        assert(data.subrange(0, a - 32768) + d =~= p);
    }
    assert(Seq::<u8>::empty() + p =~= p);
    lemma_piece_join(j, v, Seq::empty(), p, c);
    assert(p + c =~= data.subrange(0, b));
}

/// Compresses `data` at `level` (0 to 9) into one stream of format `fmt`
/// on up to `threads` threads, in chunks of `chunk` bytes, with matches
/// reaching back at most `2^wbits` bytes. The output decompresses to
/// exactly `data`, whatever the threads did.
pub fn compress(fmt: Format, data: &[u8], level: u32, wbits: u32, chunk: usize, threads: usize) -> (r: Vec<u8>)
    requires
        8 <= wbits <= 15,
        chunk >= MIN_CHUNK,
    ensures
        crate::wrap::spec_decompress(fmt, r@) == Some((data@, r@.len() as int)),
{
    hide(inflate_blocks);
    hide(end_ok);
    let len = data.len();
    let level = if level > 9 { 9 } else { level };
    let n = chunks(len, chunk);
    if n == usize::MAX {
        // Not reachable (a slice is shorter than that); the serial
        // compressor needs no bound on `n`.
        let d = Deflater::new(fmt, level, wbits);
        let mut d = d;
        d.write(data, Flush::None);
        let r = d.finish();
        proof {
            assert(Seq::<u8>::empty() + r@ =~= r@);
            assert(Seq::<u8>::empty() + data@ =~= data@);
        }
        return r;
    }
    let slots = run(fmt, data, level, wbits, chunk, n, threads);
    let mut out = header(fmt, level, wbits);
    let ghost head = out@;
    let ghost j = Seq::<u8>::empty();
    proof {
        lemma_piece_empty(Seq::empty());
        assert((0 - 1 + 1) * chunk == 0) by (nonlinear_arith);
        assert(chunk_end(len as int, chunk as int, -1) == 0);
        assert(data@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(head + j =~= head);
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n < usize::MAX,
            len == data@.len(),
            8 <= wbits <= 15,
            chunk >= MIN_CHUNK,
            n >= 1 ==> (n - 1) * chunk < len,
            n * chunk >= len,
            slots@.len() == n + 1,
            forall|k: int| 0 <= k <= n ==> (#[trigger] slots@[k] matches Some(v) ==> job_ok(fmt, data@, chunk as int, k, v@)),
            out@ == head + j,
            is_piece(j, Seq::empty(), data@.subrange(0, chunk_end(len as int, chunk as int, i - 1))),
        decreases n - i,
    {
        proof {
            assert(i * chunk <= (n - 1) * chunk) by (nonlinear_arith)
                requires
                    i <= n - 1,
                    chunk >= 0,
            ;
        }
        let fallback: Vec<u8>;
        let v: &Vec<u8> = match &slots[i + 1] {
            Some(v) => v,
            None => {
                fallback = job(fmt, data, level, wbits, chunk, i + 1);
                &fallback
            },
        };
        proof {
            assert(job_ok(fmt, data@, chunk as int, i + 1, v@));
            lemma_step(fmt, data@, chunk as int, i as int, j, v@);
            assert((head + j) + v@ =~= head + (j + v@));
            j = j + v@;
        }
        verilith_core::prims::extend(&mut out, v.as_slice());
        i = i + 1;
    }
    let fallback: Vec<u8>;
    let e: &Vec<u8> = match &slots[0] {
        Some(v) => v,
        None => {
            fallback = job(fmt, data, level, wbits, chunk, 0);
            &fallback
        },
    };
    proof {
        assert(chunk_end(len as int, chunk as int, n - 1) == len) by {
            assert((n - 1 + 1) * chunk == n * chunk) by (nonlinear_arith);
        }
        assert(data@.subrange(0, len as int) =~= data@);
        assert(job_ok(fmt, data@, chunk as int, 0, e@));
        lemma_joined(fmt, head, j, e@, data@);
    }
    verilith_core::prims::extend(&mut out, e.as_slice());
    out
}

} // verus!

/// The threads `compress_auto` uses: what `set_threads` or, failing that,
/// the environment variable `VZLIB_THREADS` says; 1 (no threads) if
/// neither does. 0 in either place means one thread per CPU.
static THREADS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(usize::MAX);

/// Sets how many threads compression may use from now on, process-wide:
/// 1 for none (the default), 0 for one per CPU.
pub fn set_threads(n: usize) {
    let n = if n == 0 { std::thread::available_parallelism().map_or(1, |c| c.get()) } else { n };
    THREADS.store(n.min(usize::MAX - 1), std::sync::atomic::Ordering::Relaxed);
}

/// The number of threads compression may use.
pub fn threads() -> usize {
    let t = THREADS.load(std::sync::atomic::Ordering::Relaxed);
    if t != usize::MAX {
        return t;
    }
    let n = std::env::var("VZLIB_THREADS").ok().and_then(|v| v.trim().parse::<usize>().ok()).unwrap_or(1);
    set_threads(n);
    THREADS.load(std::sync::atomic::Ordering::Relaxed)
}

/// Whether an input of `len` bytes at `level` is compressed in parallel:
/// threads are allowed, there are at least two chunks, and the level
/// compresses at all.
pub fn wanted(len: usize, level: u32) -> bool {
    level > 0 && len >= 2 * CHUNK && threads() > 1
}
