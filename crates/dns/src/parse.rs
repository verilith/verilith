//! The parser, proven to compute exactly `spec::parse_message`. Verus also
//! proves every index in bounds and every arithmetic operation free of
//! overflow, so it cannot panic.
use alloc::vec::Vec;
#[cfg(verus_only)]
use crate::lemmas::*;
use crate::message::*;
use crate::rdata::canon_into;
use crate::spec::*;
#[allow(unused_imports)]
use crate::spec_rdata::*;
pub use verilith_core::bytes::{read_u16, read_u32};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Appends `s` to `out` with a single `memcpy`.
pub fn append(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    out.extend_from_slice(s);
    proof {
        assert forall|i: int| 0 <= i < final(out)@.len() implies #[trigger] final(out)@[i] == (old(
            out,
        )@ + s@)[i] by {
            if i >= old(out)@.len() {
                assert(cloned::<u8>(s@[i - old(out)@.len()], final(out)@[i]));
            }
        }
        assert(final(out)@ =~= old(out)@ + s@);
    }
}

/// What the whole name decodes to, given the labels decoded so far, the
/// saved continuation offset (set at the first pointer), and what the rest
/// of the current segment decodes to.
pub open spec fn combine(acc: SpecName, saved: Option<usize>, r: Option<(SpecName, int)>) -> Option<
    (SpecName, int),
> {
    match r {
        None => None,
        Some((rest, e)) => Some(
            (
                acc + rest,
                match saved {
                    Some(s) => s as int,
                    None => e,
                },
            ),
        ),
    }
}

proof fn lemma_name_len_monotone(acc: SpecName, rest: SpecName)
    requires
        rest.len() > 0,
    ensures
        ser_name(acc + rest).len() >= ser_labels(acc).len() + 1 + rest[0].len() + 1,
{
    lemma_ser_labels_append(acc, rest);
}

/// The 14-bit offset a compression pointer at `q` targets.
pub open spec fn ptr_target(b: Seq<u8>, q: int) -> int {
    (b[q] as int - 192) * 256 + b[q + 1] as int
}

/// Most loop iterations `read_name_into` can take: one per label, one per
/// pointer followed, plus the final one.
pub spec const MAX_NAME_STEPS: nat = 256;

/// Decodes a possibly compressed name at `pos` (RFC 1035 §4.1.4) and appends
/// its uncompressed wire form to `arena`.
///
/// Never panics and always terminates. Besides matching `parse_name`, the
/// loop invariants prove (RFC 9267 §2):
/// - every pointer followed has a distinct location, so no pointer is
///   followed more than once;
/// - there are at most as many pointers as labels, so the loop runs at most
///   `MAX_NAME_STEPS` times and copies at most 255 bytes.
pub fn read_name_into(b: &[u8], pos: usize, arena: &mut Vec<u8>) -> (r: Option<
    (usize, Ghost<SpecName>),
>)
    ensures
        r matches Some((end, n)) ==> {
            &&& parse_name(b@, pos as int) == Some((n@, end as int))
            &&& final(arena)@ == old(arena)@ + ser_name(n@)
        },
        r is None ==> parse_name(b@, pos as int) is None,
        is_prefix(old(arena)@, final(arena)@),
{
    if pos >= b.len() {
        proof {
            lemma_prefix_refl(arena@);
        }
        return None;
    }
    // Labels are copied a run at a time: `run` holds the labels decoded in
    // the current segment, which sit contiguously in `b[seg..p]`, and
    // `flushed` the ones already copied to the arena.
    let ghost mut acc: SpecName = Seq::empty();
    let ghost mut flushed: SpecName = Seq::empty();
    let ghost mut run: SpecName = Seq::empty();
    let mut p = pos;
    let mut seg = pos;
    let mut saved: Option<usize> = None;
    // Wire length of the labels decoded so far, plus the root octet.
    let mut wire: usize = 1;
    // Locations of the pointers followed so far, and the step count.
    let ghost mut ptrs: Seq<int> = Seq::empty();
    let ghost mut steps: nat = 0;
    let ghost mut just_jumped = false;
    proof {
        assert(arena@ =~= old(arena)@ + ser_labels(flushed));
        assert(acc =~= flushed + run);
        assert(b@.subrange(seg as int, p as int) =~= ser_labels(run));
        lemma_prefix_refl(arena@);
        assert(parse_labels(b@, pos as int, pos as int) == combine(
            acc,
            saved,
            parse_labels(b@, p as int, seg as int),
        )) by {
            if let Some((rest, e)) = parse_labels(b@, p as int, seg as int) {
                assert(Seq::<Seq<u8>>::empty() + rest =~= rest);
            }
        }
    }
    loop
        invariant
            seg <= p,
            p <= b@.len(),
            acc == flushed + run,
            arena@ == old(arena)@ + ser_labels(flushed),
            b@.subrange(seg as int, p as int) == ser_labels(run),
            is_prefix(old(arena)@, arena@),
            wire == ser_name(acc).len(),
            wire <= MAX_NAME_WIRE_LEN,
            parse_labels(b@, pos as int, pos as int) == combine(
                acc,
                saved,
                parse_labels(b@, p as int, seg as int),
            ),
            // Pointers land on labels, so jumps never outnumber labels.
            just_jumped ==> p < b@.len() && b@[p as int] < 64,
            ptrs.len() <= acc.len() + (if just_jumped { 1int } else { 0 }),
            2 * acc.len() + 1 <= wire,
            steps == acc.len() + ptrs.len(),
            steps < MAX_NAME_STEPS,
            // Each pointer followed was at a distinct location, targeting
            // strictly decreasing offsets, the last of which is `seg`.
            forall|i: int|
                0 <= i < ptrs.len() ==> 0 <= #[trigger] ptrs[i] && ptrs[i] + 1 < b@.len(),
            forall|i: int, j: int|
                #![trigger ptrs[i], ptrs[j]]
                0 <= i < j < ptrs.len() ==> ptr_target(b@, ptrs[j]) < ptr_target(
                    b@,
                    ptrs[i],
                ),
            forall|i: int, j: int|
                #![trigger ptrs[i], ptrs[j]]
                0 <= i < j < ptrs.len() ==> ptrs[i] != ptrs[j],
            ptrs.len() > 0 ==> ptr_target(b@, ptrs.last()) == seg,
        decreases seg, b@.len() - p,
    {
        if p >= b.len() {
            return None;
        }
        let c = b[p];
        if c == 0 {
            let end = match saved {
                Some(s) => s,
                None => p + 1,
            };
            append(arena, slice_subrange(b, seg, p));
            arena.push(0u8);
            proof {
                lemma_ser_labels_append(flushed, run);
                assert(acc + Seq::<Seq<u8>>::empty() =~= acc);
                assert(arena@ =~= old(arena)@ + ser_name(acc));
                lemma_prefix_append(old(arena)@, ser_name(acc));
            }
            return Some((end, Ghost(acc)));
        } else if c >= 192 {
            if p + 1 >= b.len() {
                return None;
            }
            let target = ((c - 192) as usize) * 256 + b[p + 1] as usize;
            if target >= seg {
                return None;
            }
            if b[target] >= 64 {
                return None;
            }
            if saved.is_none() {
                saved = Some(p + 2);
            }
            proof {
                let q = p as int;
                assert(ptr_target(b@, q) == target);
                let old_ptrs = ptrs;
                ptrs = ptrs.push(q);
                assert forall|i: int, j: int|
                    #![trigger ptrs[i], ptrs[j]]
                    0 <= i < j < ptrs.len() implies ptr_target(b@, ptrs[j]) < ptr_target(
                        b@,
                        ptrs[i],
                    ) by {
                    if j == ptrs.len() - 1 && j > 0 {
                        if i < j - 1 {
                            assert(ptr_target(b@, old_ptrs[j - 1]) < ptr_target(
                                b@,
                                old_ptrs[i],
                            ));
                        }
                    }
                }
                // Same location means same target, and targets are distinct.
                assert forall|i: int, j: int|
                    #![trigger ptrs[i], ptrs[j]]
                    0 <= i < j < ptrs.len() implies ptrs[i] != ptrs[j] by {
                    assert(ptr_target(b@, ptrs[j]) < ptr_target(b@, ptrs[i]));
                }
                steps = steps + 1;
                just_jumped = true;
            }
            append(arena, slice_subrange(b, seg, p));
            proof {
                lemma_ser_labels_append(flushed, run);
                assert(arena@ =~= old(arena)@ + ser_labels(acc));
                lemma_prefix_append(old(arena)@, ser_labels(acc));
                flushed = acc;
                run = Seq::empty();
                assert(acc =~= flushed + run);
                assert(b@.subrange(target as int, target as int) =~= ser_labels(run));
            }
            p = target;
            seg = target;
        } else if c >= 64 {
            return None;
        } else {
            let len = c as usize;
            if len > b.len() - (p + 1) {
                return None;
            }
            if wire + 1 + len > 255 {
                proof {
                    if let Some((rest, e)) = parse_labels(b@, (p + 1 + len) as int, seg as int) {
                        let l = b@.subrange(p + 1, p + 1 + len);
                        lemma_name_len_monotone(acc, seq![l] + rest);
                        lemma_ser_labels_append(acc, Seq::empty());
                        assert(acc + Seq::<Seq<u8>>::empty() =~= acc);
                    }
                }
                return None;
            }
            let ghost l = b@.subrange(p + 1, p + 1 + len);
            proof {
                assert(b@.subrange(p as int, p + 1 + len) =~= ser_label(l));
                lemma_ser_labels_push(acc, l);
                lemma_ser_labels_push(run, l);
                assert(b@.subrange(seg as int, p + 1 + len) =~= b@.subrange(seg as int, p as int)
                    + b@.subrange(p as int, p + 1 + len));
                if let Some((rest, e)) = parse_labels(b@, (p + 1 + len) as int, seg as int) {
                    assert(acc + (seq![l] + rest) =~= acc.push(l) + rest);
                }
                acc = acc.push(l);
                run = run.push(l);
                assert(acc =~= flushed + run);
                steps = steps + 1;
                just_jumped = false;
            }
            wire = wire + 1 + len;
            p = p + 1 + len;
        }
    }
}

proof fn lemma_new_span(old_arena: Seq<u8>, x: Seq<u8>)
    requires
        old_arena.len() + x.len() <= usize::MAX,
    ensures
        span_ok(old_arena + x, Span { start: old_arena.len() as usize, len: x.len() as usize }, x),
{
    assert((old_arena + x).subrange(old_arena.len() as int, (old_arena.len() + x.len()) as int)
        =~= x);
}

/// Arena bytes below the input's length are the input itself.
proof fn lemma_prefix_sub(b: Seq<u8>, a: Seq<u8>, i: int, j: int)
    requires
        is_prefix(b, a),
        0 <= i <= j <= b.len(),
    ensures
        a.subrange(i, j) == b.subrange(i, j),
{
    assert(a.subrange(i, j) =~= a.subrange(0, b.len() as int).subrange(i, j));
}

/// Decodes the name at `pos` onto the end of the arena and returns its span.
fn read_name_span(b: &[u8], pos: usize, arena: &mut Vec<u8>) -> (r: Option<
    (Span, usize, Ghost<SpecName>),
>)
    ensures
        r matches Some((sp, end, n)) ==> {
            &&& parse_name(b@, pos as int) == Some((n@, end as int))
            &&& span_ok(final(arena)@, sp, ser_name(n@))
        },
        r is None ==> parse_name(b@, pos as int) is None,
        is_prefix(old(arena)@, final(arena)@),
{
    let start = arena.len();
    let (end, n) = match read_name_into(b, pos, arena) {
        Some(x) => x,
        None => return None,
    };
    let sp = Span { start, len: arena.len() - start };
    proof {
        lemma_new_span(old(arena)@, ser_name(n@));
        lemma_prefix_append(old(arena)@, ser_name(n@));
    }
    Some((sp, end, n))
}

fn read_question(b: &[u8], pos: usize, arena: &mut Vec<u8>) -> (r: Option<
    (Entry, usize, Ghost<SpecQuestion>),
>)
    requires
        is_prefix(b@, old(arena)@),
    ensures
        r matches Some((e, end, g)) ==> {
            &&& parse_question(b@, pos as int) == Some((g@, end as int))
            &&& is_prefix(old(arena)@, final(arena)@)
            &&& question_ok(final(arena)@, e, g@)
        },
        r is None ==> parse_question(b@, pos as int) is None,
{
    let (name, p1, n) = match read_name_span(b, pos, arena) {
        Some(x) => x,
        None => return None,
    };
    let (qtype, p2) = match read_u16(b, p1) {
        Some(x) => x,
        None => return None,
    };
    let (qclass, p3) = match read_u16(b, p2) {
        Some(x) => x,
        None => return None,
    };
    let e = Entry { name, rtype: qtype, rclass: qclass, ttl: 0, rdata: Span { start: 0, len: 0 } };
    Some((e, p3, Ghost(SpecQuestion { qname: n@, qtype, qclass })))
}

/// A name already decoded into the arena: the offset it was decoded from
/// and its span. `memo_ok` says the span holds what decoding that offset
/// gives.
pub open spec fn memo_ok(b: Seq<u8>, arena: Seq<u8>, memo: Option<(usize, Span)>, n: SpecName) -> bool {
    match memo {
        None => true,
        Some((off, sp)) => {
            &&& (match parse_name(b, off as int) {
                Some((m, _)) => m == n,
                None => false,
            })
            &&& span_ok(arena, sp, ser_name(n))
        },
    }
}

/// Decodes the name at `pos` into the arena, except that a name which is
/// exactly a compression pointer to a memoized offset reuses the memoized
/// span: no decoding and no copy. `memo` is fixed (the question name, which
/// answer owner names usually point to) and `last` is the target of the last
/// such pointer decoded (authority owner names usually all point to the
/// zone apex, a suffix of the question name).
fn read_owner(
    b: &[u8],
    pos: usize,
    arena: &mut Vec<u8>,
    memo: Option<(usize, Span)>,
    memo_name: Ghost<SpecName>,
    last: &mut Option<(usize, Span)>,
    last_name: &mut Ghost<SpecName>,
) -> (r: Option<(Span, usize, Ghost<SpecName>)>)
    requires
        memo_ok(b@, old(arena)@, memo, memo_name@),
        memo_ok(b@, old(arena)@, *old(last), old(last_name)@),
        is_prefix(b@, old(arena)@),
    ensures
        r matches Some((sp, end, n)) ==> {
            &&& parse_name(b@, pos as int) == Some((n@, end as int))
            &&& span_ok(final(arena)@, sp, ser_name(n@))
        },
        r is None ==> parse_name(b@, pos as int) is None,
        is_prefix(old(arena)@, final(arena)@),
        memo_ok(b@, final(arena)@, *final(last), final(last_name)@),
{
    if pos < b.len() && b.len() - pos >= 2 && b[pos] >= 192 {
        let target = ((b[pos] - 192) as usize) * 256 + b[pos + 1] as usize;
        if target < pos {
            let t = b[target];
            if t != 0 && t < 64 {
                if let Some((off, sp)) = memo {
                    if target == off {
                        proof {
                            lemma_prefix_refl(arena@);
                            assert(parse_labels(b@, pos as int, pos as int) matches Some((m, e))
                                && m == memo_name@ && e == pos + 2);
                        }
                        return Some((sp, pos + 2, memo_name));
                    }
                }
                if let Some((off, sp)) = *last {
                    if target == off {
                        proof {
                            lemma_prefix_refl(arena@);
                            assert(parse_labels(b@, pos as int, pos as int) matches Some((m, e))
                                && m == last_name@ && e == pos + 2);
                        }
                        return Some((sp, pos + 2, *last_name));
                    }
                }
                let ghost a0 = arena@;
                let r = read_name_span(b, pos, arena);
                match r {
                    Some((sp, end, n)) => {
                        proof {
                            assert(parse_labels(b@, target as int, target as int) matches Some((
                                m,
                                _,
                            )) && m == n@);
                        }
                        *last = Some((target, sp));
                        *last_name = n;
                    },
                    None => {
                        proof {
                            lemma_memo_grow(b@, a0, arena@, *last, last_name@);
                        }
                    },
                }
                return r;
            }
        }
    }
    let ghost a0 = arena@;
    let r = read_name_span(b, pos, arena);
    proof {
        lemma_memo_grow(b@, a0, arena@, *last, last_name@);
    }
    r
}

fn read_record(
    b: &[u8],
    pos: usize,
    arena: &mut Vec<u8>,
    memo: Option<(usize, Span)>,
    memo_name: Ghost<SpecName>,
    last: &mut Option<(usize, Span)>,
    last_name: &mut Ghost<SpecName>,
) -> (r: Option<(Entry, usize, Ghost<SpecRecord>)>)
    requires
        memo_ok(b@, old(arena)@, memo, memo_name@),
        memo_ok(b@, old(arena)@, *old(last), old(last_name)@),
        is_prefix(b@, old(arena)@),
    ensures
        r matches Some((e, end, g)) ==> {
            &&& parse_record(b@, pos as int) == Some((g@, end as int))
            &&& record_ok(final(arena)@, e, g@)
        },
        r is None ==> parse_record(b@, pos as int) is None,
        is_prefix(old(arena)@, final(arena)@),
        memo_ok(b@, final(arena)@, *final(last), final(last_name)@),
{
    let (name, p1, n) = match read_owner(b, pos, arena, memo, memo_name, last, last_name) {
        Some(x) => x,
        None => return None,
    };
    let ghost a1 = arena@;
    let (rtype, p2) = match read_u16(b, p1) {
        Some(x) => x,
        None => return None,
    };
    let (rclass, p3) = match read_u16(b, p2) {
        Some(x) => x,
        None => return None,
    };
    let (ttl, p4) = match read_u32(b, p3) {
        Some(x) => x,
        None => return None,
    };
    let (rdlen, p5) = match read_u16(b, p4) {
        Some(x) => x,
        None => return None,
    };
    if rdlen as usize > b.len() - p5 {
        return None;
    }
    let end = p5 + rdlen as usize;
    let ghost data = canon_rdata(b@, rtype, p5 as int, end as int).unwrap();
    let rdata = if is_compressible(rtype) {
        // Names inside the RDATA are decompressed onto the arena.
        let start = arena.len();
        let ok = canon_into(b, rtype, p5, end, arena);
        proof {
            lemma_prefix_trans(old(arena)@, a1, arena@);
            lemma_memo_grow(b@, a1, arena@, *last, last_name@);
        }
        if !ok || arena.len() - start > 65535 {
            return None;
        }
        proof {
            lemma_new_span(a1, data);
            lemma_span_ok_grow(a1, arena@, name, ser_name(n@));
        }
        Span { start, len: arena.len() - start }
    } else {
        // Other RDATA stays where it is in the input copy.
        proof {
            lemma_prefix_trans(b@, old(arena)@, arena@);
            lemma_prefix_sub(b@, arena@, p5 as int, end as int);
            lemma_prefix_refl(arena@);
        }
        Span { start: p5, len: rdlen as usize }
    };
    Some(
        (
            Entry { name, rtype, rclass, ttl, rdata },
            end,
            Ghost(SpecRecord { name: n@, rtype, rclass, ttl, rdata: data }),
        ),
    )
}

/// Whether names inside RDATA of type `t` may be compressed.
#[inline(always)]
pub fn is_compressible(t: u16) -> (r: bool)
    ensures
        r == compressible(t),
{
    t == 2 || t == 5 || t == 6 || t == 12 || t == 15 || t == 24 || t == 33 || t == 35
}

pub open spec fn prepend<T>(acc: Seq<T>, r: Option<(Seq<T>, int)>) -> Option<(Seq<T>, int)> {
    match r {
        None => None,
        Some((rest, e)) => Some((acc + rest, e)),
    }
}

/// Parses `n` questions at `pos`, appending them to `entries`.
fn read_questions(
    b: &[u8],
    pos: usize,
    n: u16,
    arena: &mut Vec<u8>,
    entries: &mut Vec<Entry>,
) -> (r: Option<(usize, Ghost<Seq<SpecQuestion>>)>)
    requires
        is_prefix(b@, old(arena)@),
    ensures
        r matches Some((end, g)) ==> {
            &&& parse_questions(b@, pos as int, n as nat) == Some((g@, end as int))
            &&& is_prefix(old(arena)@, final(arena)@)
            &&& is_prefix(old(entries)@, final(entries)@)
            &&& final(entries)@.len() == old(entries)@.len() + n
            &&& questions_at(final(arena)@, final(entries)@, old(entries)@.len() as int, g@)
        },
        r is None ==> parse_questions(b@, pos as int, n as nat) is None,
{
    let ghost off = entries@.len() as int;
    let ghost mut g: Seq<SpecQuestion> = Seq::empty();
    let mut p = pos;
    let mut i: u16 = 0;
    proof {
        lemma_prefix_refl(arena@);
        lemma_prefix_refl(entries@);
        lemma_prefix_trans(b@, old(arena)@, arena@);
        if let Some((rest, e)) = parse_questions(b@, pos as int, n as nat) {
            assert(g + rest =~= rest);
        }
    }
    while i < n
        invariant
            i <= n,
            g.len() == i,
            off == old(entries)@.len(),
            entries@.len() == off + i,
            parse_questions(b@, pos as int, n as nat) == prepend(
                g,
                parse_questions(b@, p as int, (n - i) as nat),
            ),
            is_prefix(old(arena)@, arena@),
            is_prefix(b@, arena@),
            is_prefix(old(entries)@, entries@),
            questions_at(arena@, entries@, off, g),
        decreases n - i,
    {
        let ghost a0 = arena@;
        let ghost e0 = entries@;
        let (e, p2, gq) = match read_question(b, p, arena) {
            Some(x) => x,
            None => return None,
        };
        proof {
            if let Some((rest, e)) = parse_questions(b@, p2 as int, (n - i - 1) as nat) {
                assert(g + (seq![gq@] + rest) =~= g.push(gq@) + rest);
            }
        }
        entries.push(e);
        proof {
            lemma_prefix_push(e0, e);
            lemma_prefix_trans(old(entries)@, e0, entries@);
            lemma_prefix_trans(old(arena)@, a0, arena@);
            lemma_prefix_trans(b@, a0, arena@);
            lemma_questions_at_grow(a0, arena@, e0, entries@, off, g);
            let g2 = g.push(gq@);
            assert forall|k: int| 0 <= k < g2.len() implies question_ok(
                arena@,
                #[trigger] entries@[off + k],
                g2[k],
            ) by {
                if k < g.len() {
                    assert(question_ok(arena@, entries@[off + k], g[k]));
                }
            }
            g = g2;
        }
        p = p2;
        i = i + 1;
    }
    proof {
        assert(g + Seq::empty() =~= g);
    }
    Some((p, Ghost(g)))
}

/// Parses `n` records at `pos`, appending them to `entries`.
proof fn lemma_memo_grow(b: Seq<u8>, a: Seq<u8>, a2: Seq<u8>, memo: Option<(usize, Span)>, n: SpecName)
    requires
        is_prefix(a, a2),
        memo_ok(b, a, memo, n),
    ensures
        memo_ok(b, a2, memo, n),
{
    if let Some((off, sp)) = memo {
        lemma_span_ok_grow(a, a2, sp, ser_name(n));
    }
}

fn read_records(
    b: &[u8],
    pos: usize,
    n: u16,
    arena: &mut Vec<u8>,
    entries: &mut Vec<Entry>,
    memo: Option<(usize, Span)>,
    memo_name: Ghost<SpecName>,
) -> (r: Option<(usize, Ghost<Seq<SpecRecord>>)>)
    requires
        memo_ok(b@, old(arena)@, memo, memo_name@),
        is_prefix(b@, old(arena)@),
    ensures
        r matches Some((end, g)) ==> {
            &&& parse_records(b@, pos as int, n as nat) == Some((g@, end as int))
            &&& is_prefix(old(arena)@, final(arena)@)
            &&& is_prefix(old(entries)@, final(entries)@)
            &&& final(entries)@.len() == old(entries)@.len() + n
            &&& records_at(final(arena)@, final(entries)@, old(entries)@.len() as int, g@)
        },
        r is None ==> parse_records(b@, pos as int, n as nat) is None,
{
    let ghost off = entries@.len() as int;
    let ghost mut g: Seq<SpecRecord> = Seq::empty();
    let mut p = pos;
    let mut last: Option<(usize, Span)> = None;
    let mut last_name: Ghost<SpecName> = Ghost(Seq::empty());
    let mut i: u16 = 0;
    proof {
        lemma_prefix_refl(arena@);
        lemma_prefix_refl(entries@);
        lemma_prefix_trans(b@, old(arena)@, arena@);
        if let Some((rest, e)) = parse_records(b@, pos as int, n as nat) {
            assert(g + rest =~= rest);
        }
    }
    while i < n
        invariant
            i <= n,
            g.len() == i,
            off == old(entries)@.len(),
            entries@.len() == off + i,
            parse_records(b@, pos as int, n as nat) == prepend(
                g,
                parse_records(b@, p as int, (n - i) as nat),
            ),
            is_prefix(old(arena)@, arena@),
            is_prefix(b@, arena@),
            is_prefix(old(entries)@, entries@),
            records_at(arena@, entries@, off, g),
            memo_ok(b@, arena@, memo, memo_name@),
            memo_ok(b@, arena@, last, last_name@),
        decreases n - i,
    {
        let ghost a0 = arena@;
        let ghost e0 = entries@;
        let (e, p2, gr) = match read_record(b, p, arena, memo, memo_name, &mut last, &mut last_name) {
            Some(x) => x,
            None => return None,
        };
        proof {
            lemma_memo_grow(b@, a0, arena@, memo, memo_name@);
        }
        proof {
            if let Some((rest, e)) = parse_records(b@, p2 as int, (n - i - 1) as nat) {
                assert(g + (seq![gr@] + rest) =~= g.push(gr@) + rest);
            }
        }
        entries.push(e);
        proof {
            lemma_prefix_push(e0, e);
            lemma_prefix_trans(old(entries)@, e0, entries@);
            lemma_prefix_trans(old(arena)@, a0, arena@);
            lemma_prefix_trans(b@, a0, arena@);
            lemma_records_at_grow(a0, arena@, e0, entries@, off, g);
            let g2 = g.push(gr@);
            assert forall|k: int| 0 <= k < g2.len() implies record_ok(
                arena@,
                #[trigger] entries@[off + k],
                g2[k],
            ) by {
                if k < g.len() {
                    assert(record_ok(arena@, entries@[off + k], g[k]));
                }
            }
            g = g2;
        }
        p = p2;
        i = i + 1;
    }
    proof {
        assert(g + Seq::empty() =~= g);
    }
    Some((p, Ghost(g)))
}

/// What `parse_with` has once every section is read: the message the
/// spec decodes, laid out in the final arena and entry table. Proved apart
/// from the exec body, whose many buffer snapshots make this expensive there.
#[verifier::spinoff_prover]
proof fn lemma_parse_with_parts(
    b: Seq<u8>,
    m: SpecMessage,
    qd: u16,
    an: u16,
    ns: u16,
    ar: u16,
    p1: int,
    p2: int,
    p3: int,
    a1: Seq<u8>,
    a2: Seq<u8>,
    a3: Seq<u8>,
    a: Seq<u8>,
    e1: Seq<Entry>,
    e2: Seq<Entry>,
    e3: Seq<Entry>,
    e: Seq<Entry>,
)
    requires
        b.len() >= 12,
        parse_u16(b, 0) == Some((m.id, 2int)),
        parse_u16(b, 2) == Some((m.flags, 4int)),
        parse_u16(b, 4) == Some((qd, 6int)),
        parse_u16(b, 6) == Some((an, 8int)),
        parse_u16(b, 8) == Some((ns, 10int)),
        parse_u16(b, 10) == Some((ar, 12int)),
        parse_questions(b, 12, qd as nat) == Some((m.questions, p1)),
        parse_records(b, p1, an as nat) == Some((m.answers, p2)),
        parse_records(b, p2, ns as nat) == Some((m.authorities, p3)),
        parse_records(b, p3, ar as nat) == Some((m.additionals, b.len() as int)),
        is_prefix(b, a1),
        is_prefix(a1, a2),
        is_prefix(a2, a3),
        is_prefix(a3, a),
        is_prefix(e1, e2),
        is_prefix(e2, e3),
        is_prefix(e3, e),
        e1.len() == qd,
        e2.len() == e1.len() + an,
        e3.len() == e2.len() + ns,
        e.len() == e3.len() + ar,
        questions_at(a1, e1, 0, m.questions),
        records_at(a2, e2, qd as int, m.answers),
        records_at(a3, e3, qd + an, m.authorities),
        records_at(a, e, qd + an + ns, m.additionals),
    ensures
        parse_message(b) == Some(m),
        parts_ok(m.id, m.flags, a, e, qd as usize, an as usize, ns as usize, m),
        b.len() <= a.len(),
        a.subrange(0, b.len() as int) == b,
{
    theorem_parse_valid(b);
    lemma_prefix_trans(b, a1, a2);
    lemma_prefix_trans(b, a2, a3);
    lemma_prefix_trans(b, a3, a);
    lemma_prefix_trans(a1, a2, a3);
    lemma_prefix_trans(a1, a3, a);
    lemma_prefix_trans(a2, a3, a);
    lemma_prefix_trans(e1, e2, e3);
    lemma_prefix_trans(e1, e3, e);
    lemma_prefix_trans(e2, e3, e);
    lemma_questions_at_grow(a1, a, e1, e, 0, m.questions);
    lemma_records_at_grow(a2, a, e2, e, qd as int, m.answers);
    lemma_records_at_grow(a3, a, e3, e, qd + an, m.authorities);
    lemma_parse_questions_valid(b, 12, qd as nat);
    lemma_parse_records_valid(b, p1, an as nat);
    lemma_parse_records_valid(b, p2, ns as nat);
    lemma_parse_records_valid(b, p3, ar as nat);
}

/// Parses `b` using the given (empty) buffers. On failure, hands the buffers
/// back so their capacity can be reused.
#[verifier::spinoff_prover]
fn parse_with(b: &[u8], arena: Vec<u8>, entries: Vec<Entry>) -> (r: Result<
    Message,
    (Vec<u8>, Vec<Entry>),
>)
    requires
        arena@.len() == 0,
        entries@.len() == 0,
    ensures
        r matches Ok(m) ==> parse_message(b@) == Some(m@) && m.wire_bytes() == b@,
        r is Err ==> parse_message(b@) is None,
{
    let mut arena = arena;
    let mut entries = entries;
    if b.len() < 12 {
        return Err((arena, entries));
    }
    let id = read_u16(b, 0).unwrap().0;
    let flags = read_u16(b, 2).unwrap().0;
    let qd = read_u16(b, 4).unwrap().0;
    let an = read_u16(b, 6).unwrap().0;
    let ns = read_u16(b, 8).unwrap().0;
    let ar = read_u16(b, 10).unwrap().0;
    // RFC 9267 §6: check the counts against the message size before parsing.
    // A question takes at least 5 bytes and a record at least 11, so counts
    // that cannot fit are rejected without decoding (or allocating) anything.
    let total = qd as usize + an as usize + ns as usize + ar as usize;
    if 5 * (qd as usize) + 11 * (an as usize + ns as usize + ar as usize) > b.len() - 12 {
        proof {
            lemma_counts_fit(b@);
        }
        return Err((arena, entries));
    }
    entries.reserve(total);
    // The arena starts with a copy of the input, so each RDATA is a span
    // into it, and decoded names follow it. Names usually expand under
    // decompression; reserving twice the input avoids most regrowth.
    arena.reserve(
        if b.len() <= 0x1_0000 {
            2 * b.len()
        } else {
            b.len()
        },
    );
    append(&mut arena, b);
    proof {
        assert(arena@ =~= b@);
        lemma_prefix_refl(b@);
    }
    let ghost a0 = arena@;
    let ghost e0 = entries@;
    let (p1, gq) = match read_questions(b, 12, qd, &mut arena, &mut entries) {
        Some(x) => x,
        None => return Err((arena, entries)),
    };
    let ghost a1 = arena@;
    let ghost e1 = entries@;
    // Answer owner names usually point at the first question's name.
    let memo = if qd > 0 {
        Some((12usize, entries[0].name))
    } else {
        None
    };
    let ghost memo_name = if qd > 0 {
        gq@[0].qname
    } else {
        Seq::empty()
    };
    proof {
        if qd > 0 {
            assert(question_ok(a1, e1[0int + 0int], gq@[0]));
            let pq = parse_question(b@, 12);
            assert(pq is Some);
            assert(pq.unwrap().0 == gq@[0]);
        }
    }
    let (p2, gan) = match read_records(b, p1, an, &mut arena, &mut entries, memo, Ghost(memo_name)) {
        Some(x) => x,
        None => return Err((arena, entries)),
    };
    let ghost a2 = arena@;
    let ghost e2 = entries@;
    proof {
        lemma_memo_grow(b@, a1, arena@, memo, memo_name);
        lemma_prefix_trans(b@, a0, a1);
        lemma_prefix_trans(b@, a1, arena@);
    }
    let (p3, gns) = match read_records(b, p2, ns, &mut arena, &mut entries, memo, Ghost(memo_name)) {
        Some(x) => x,
        None => return Err((arena, entries)),
    };
    let ghost a3 = arena@;
    let ghost e3 = entries@;
    proof {
        lemma_memo_grow(b@, a2, arena@, memo, memo_name);
        lemma_prefix_trans(b@, a2, arena@);
    }
    let (end, gar) = match read_records(b, p3, ar, &mut arena, &mut entries, memo, Ghost(memo_name)) {
        Some(x) => x,
        None => return Err((arena, entries)),
    };
    if end != b.len() {
        return Err((arena, entries));
    }
    let ghost spec = SpecMessage {
        id,
        flags,
        questions: gq@,
        answers: gan@,
        authorities: gns@,
        additionals: gar@,
    };
    proof {
        lemma_parse_with_parts(
            b@,
            spec,
            qd,
            an,
            ns,
            ar,
            p1 as int,
            p2 as int,
            p3 as int,
            a1,
            a2,
            a3,
            arena@,
            e1,
            e2,
            e3,
            entries@,
        );
    }
    Ok(
        Message::from_parts(
            id,
            flags,
            arena,
            entries,
            qd as usize,
            an as usize,
            ns as usize,
            b.len(),
            Ghost(spec),
        ),
    )
}

/// Parses a complete DNS message.
#[inline]
pub fn parse(b: &[u8]) -> (r: Option<Message>)
    ensures
        r matches Some(m) ==> parse_message(b@) == Some(m@) && m.wire_bytes() == b@,
        r is None ==> parse_message(b@) is None,
{
    match parse_with(b, Vec::new(), Vec::new()) {
        Ok(m) => Some(m),
        Err(_) => None,
    }
}

impl Message {
    /// Parses `b` into `self`, reusing its buffers, so a long-lived `Message`
    /// parses without allocating once its buffers have grown. On failure
    /// `self` is left as an empty message.
    pub fn parse_into(&mut self, b: &[u8]) -> (ok: bool)
        ensures
            ok ==> parse_message(b@) == Some(final(self)@) && final(self).wire_bytes() == b@,
            !ok ==> parse_message(b@) is None,
    {
        let mut taken = Message::new(0, 0);
        core::mem::swap(self, &mut taken);
        let (mut arena, mut entries) = taken.into_buffers();
        arena.clear();
        entries.clear();
        match parse_with(b, arena, entries) {
            Ok(m) => {
                *self = m;
                true
            },
            Err((mut arena, mut entries)) => {
                arena.clear();
                entries.clear();
                *self = Message::empty_with(arena, entries);
                false
            },
        }
    }
}

} // verus!
