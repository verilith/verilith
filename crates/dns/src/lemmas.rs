//! Spec-level theorems: round-trip and well-formedness of parsed values.
#[cfg(verus_only)]
use crate::lemmas_rdata::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::spec_rdata::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Helpers about byte sequences
// ---------------------------------------------------------------------------

/// `b` contains `x` at offset `pos`.
pub open spec fn at(b: Seq<u8>, pos: int, x: Seq<u8>) -> bool {
    0 <= pos && pos + x.len() <= b.len() && b.subrange(pos, pos + x.len() as int) == x
}

pub proof fn lemma_at_split(b: Seq<u8>, pos: int, x: Seq<u8>, y: Seq<u8>)
    requires
        at(b, pos, x + y),
    ensures
        at(b, pos, x),
        at(b, pos + x.len(), y),
{
    assert(b.subrange(pos, pos + x.len() as int) =~= (x + y).subrange(0, x.len() as int));
    assert(b.subrange(pos + x.len(), pos + x.len() + y.len()) =~= (x + y).subrange(
        x.len() as int,
        (x.len() + y.len()) as int,
    ));
    assert((x + y).subrange(0, x.len() as int) =~= x);
    assert((x + y).subrange(x.len() as int, (x.len() + y.len()) as int) =~= y);
}

pub proof fn lemma_at_whole(b: Seq<u8>)
    ensures
        at(b, 0, b),
{
    assert(b.subrange(0, b.len() as int) =~= b);
}

// ---------------------------------------------------------------------------
// Serializers distribute over concatenation
// ---------------------------------------------------------------------------

pub proof fn lemma_ser_labels_append(a: SpecName, c: SpecName)
    ensures
        ser_labels(a + c) == ser_labels(a) + ser_labels(c),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
        assert(ser_labels(a) + ser_labels(c) =~= ser_labels(c));
    } else {
        assert((a + c).drop_first() =~= a.drop_first() + c);
        lemma_ser_labels_append(a.drop_first(), c);
        assert((a + c)[0] == a[0]);
        assert(ser_labels(a + c) =~= ser_labels(a) + ser_labels(c));
    }
}

pub proof fn lemma_ser_questions_append(a: Seq<SpecQuestion>, c: Seq<SpecQuestion>)
    ensures
        ser_questions(a + c) == ser_questions(a) + ser_questions(c),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
        assert(ser_questions(a) + ser_questions(c) =~= ser_questions(c));
    } else {
        assert((a + c).drop_first() =~= a.drop_first() + c);
        lemma_ser_questions_append(a.drop_first(), c);
        assert((a + c)[0] == a[0]);
        assert(ser_questions(a + c) =~= ser_questions(a) + ser_questions(c));
    }
}

pub proof fn lemma_ser_records_append(a: Seq<SpecRecord>, c: Seq<SpecRecord>)
    ensures
        ser_records(a + c) == ser_records(a) + ser_records(c),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
        assert(ser_records(a) + ser_records(c) =~= ser_records(c));
    } else {
        assert((a + c).drop_first() =~= a.drop_first() + c);
        lemma_ser_records_append(a.drop_first(), c);
        assert((a + c)[0] == a[0]);
        assert(ser_records(a + c) =~= ser_records(a) + ser_records(c));
    }
}

/// Serializing `s.push(x)` appends `x`'s encoding: what the exec serializer
/// loops rely on.
pub proof fn lemma_ser_labels_push(s: SpecName, x: Seq<u8>)
    ensures
        ser_labels(s.push(x)) == ser_labels(s) + ser_label(x),
{
    lemma_ser_labels_append(s, seq![x]);
    assert(s.push(x) =~= s + seq![x]);
    let one = seq![x];
    assert(one.drop_first() =~= Seq::<Seq<u8>>::empty());
    assert(one[0] == x);
    assert(ser_labels(one) == ser_label(one[0]) + ser_labels(one.drop_first()));
    assert(ser_labels(one) =~= ser_label(x));
}

pub proof fn lemma_ser_questions_push(s: Seq<SpecQuestion>, x: SpecQuestion)
    ensures
        ser_questions(s.push(x)) == ser_questions(s) + ser_question(x),
{
    lemma_ser_questions_append(s, seq![x]);
    assert(s.push(x) =~= s + seq![x]);
    let one = seq![x];
    assert(one.drop_first() =~= Seq::<SpecQuestion>::empty());
    assert(one[0] == x);
    assert(ser_questions(one) == ser_question(one[0]) + ser_questions(one.drop_first()));
    assert(ser_questions(one) =~= ser_question(x));
}

pub proof fn lemma_ser_records_push(s: Seq<SpecRecord>, x: SpecRecord)
    ensures
        ser_records(s.push(x)) == ser_records(s) + ser_record(x),
{
    lemma_ser_records_append(s, seq![x]);
    assert(s.push(x) =~= s + seq![x]);
    let one = seq![x];
    assert(one.drop_first() =~= Seq::<SpecRecord>::empty());
    assert(one[0] == x);
    assert(ser_records(one) == ser_record(one[0]) + ser_records(one.drop_first()));
    assert(ser_records(one) =~= ser_record(x));
}

// ---------------------------------------------------------------------------
// Round trip: parse(serialize(x)) == x
// ---------------------------------------------------------------------------

pub proof fn lemma_u16_roundtrip(b: Seq<u8>, pos: int, x: u16)
    requires
        at(b, pos, ser_u16(x)),
    ensures
        parse_u16(b, pos) == Some((x, pos + 2)),
{
    assert(b[pos] == b.subrange(pos, pos + 2)[0]);
    assert(b[pos + 1] == b.subrange(pos, pos + 2)[1]);
}

pub proof fn lemma_u32_roundtrip(b: Seq<u8>, pos: int, x: u32)
    requires
        at(b, pos, ser_u32(x)),
    ensures
        parse_u32(b, pos) == Some((x, pos + 4)),
{
    let s = b.subrange(pos, pos + 4);
    assert(b[pos] == s[0]);
    assert(b[pos + 1] == s[1]);
    assert(b[pos + 2] == s[2]);
    assert(b[pos + 3] == s[3]);
}

pub proof fn lemma_labels_roundtrip(b: Seq<u8>, pos: int, seg: int, n: SpecName)
    requires
        0 <= seg <= pos,
        forall|i: int| 0 <= i < n.len() ==> valid_label(#[trigger] n[i]),
        at(b, pos, ser_name(n)),
    ensures
        parse_labels(b, pos, seg) == Some((n, pos + ser_name(n).len())),
    decreases n.len(),
{
    if n.len() == 0 {
        assert(ser_name(n) =~= seq![0u8]);
        assert(b[pos] == b.subrange(pos, pos + 1)[0]);
    } else {
        let l = n[0];
        let rest = n.drop_first();
        assert(valid_label(l));
        assert(ser_name(n) =~= seq![l.len() as u8] + (l + ser_name(rest)));
        lemma_at_split(b, pos, seq![l.len() as u8], l + ser_name(rest));
        lemma_at_split(b, pos + 1, l, ser_name(rest));
        assert(b[pos] == b.subrange(pos, pos + 1)[0]);
        assert(forall|i: int| 0 <= i < rest.len() ==> rest[i] == n[i + 1]);
        lemma_labels_roundtrip(b, pos + 1 + l.len(), seg, rest);
        assert(seq![l] + rest =~= n);
    }
}

pub proof fn lemma_name_roundtrip(b: Seq<u8>, pos: int, n: SpecName)
    requires
        valid_name(n),
        at(b, pos, ser_name(n)),
    ensures
        parse_name(b, pos) == Some((n, pos + ser_name(n).len())),
{
    lemma_labels_roundtrip(b, pos, pos, n);
}

pub proof fn lemma_question_roundtrip(b: Seq<u8>, pos: int, q: SpecQuestion)
    requires
        valid_question(q),
        at(b, pos, ser_question(q)),
    ensures
        parse_question(b, pos) == Some((q, pos + ser_question(q).len())),
{
    let n = ser_name(q.qname);
    lemma_at_split(b, pos, n + ser_u16(q.qtype), ser_u16(q.qclass));
    lemma_at_split(b, pos, n, ser_u16(q.qtype));
    lemma_name_roundtrip(b, pos, q.qname);
    lemma_u16_roundtrip(b, pos + n.len(), q.qtype);
    lemma_u16_roundtrip(b, pos + n.len() + 2, q.qclass);
}

pub proof fn lemma_record_roundtrip(b: Seq<u8>, pos: int, r: SpecRecord)
    requires
        valid_record(r),
        at(b, pos, ser_record(r)),
    ensures
        parse_record(b, pos) == Some((r, pos + ser_record(r).len())),
{
    hide(canon_rdata);
    let n = ser_name(r.name);
    let s1 = n + ser_u16(r.rtype);
    let s2 = s1 + ser_u16(r.rclass);
    let s3 = s2 + ser_u32(r.ttl);
    let s4 = s3 + ser_u16(r.rdata.len() as u16);
    lemma_at_split(b, pos, s4, r.rdata);
    lemma_at_split(b, pos, s3, ser_u16(r.rdata.len() as u16));
    lemma_at_split(b, pos, s2, ser_u32(r.ttl));
    lemma_at_split(b, pos, s1, ser_u16(r.rclass));
    lemma_at_split(b, pos, n, ser_u16(r.rtype));
    lemma_name_roundtrip(b, pos, r.name);
    lemma_u16_roundtrip(b, pos + n.len(), r.rtype);
    lemma_u16_roundtrip(b, pos + n.len() + 2, r.rclass);
    lemma_u32_roundtrip(b, pos + n.len() + 4, r.ttl);
    lemma_u16_roundtrip(b, pos + n.len() + 8, r.rdata.len() as u16);
    let p5 = pos + n.len() + 10;
    assert(b.subrange(p5, p5 + r.rdata.len()) == r.rdata);
    lemma_canon_rdata_moves(r.rdata, r.rtype, 0, r.rdata.len() as int, b, p5);
}

pub proof fn lemma_questions_roundtrip(b: Seq<u8>, pos: int, qs: Seq<SpecQuestion>)
    requires
        forall|i: int| 0 <= i < qs.len() ==> valid_question(#[trigger] qs[i]),
        at(b, pos, ser_questions(qs)),
    ensures
        parse_questions(b, pos, qs.len()) == Some((qs, pos + ser_questions(qs).len())),
    decreases qs.len(),
{
    if qs.len() > 0 {
        let rest = qs.drop_first();
        lemma_at_split(b, pos, ser_question(qs[0]), ser_questions(rest));
        lemma_question_roundtrip(b, pos, qs[0]);
        assert(forall|i: int| 0 <= i < rest.len() ==> rest[i] == qs[i + 1]);
        lemma_questions_roundtrip(b, pos + ser_question(qs[0]).len(), rest);
        assert(seq![qs[0]] + rest =~= qs);
    }
}

pub proof fn lemma_records_roundtrip(b: Seq<u8>, pos: int, rs: Seq<SpecRecord>)
    requires
        forall|i: int| 0 <= i < rs.len() ==> valid_record(#[trigger] rs[i]),
        at(b, pos, ser_records(rs)),
    ensures
        parse_records(b, pos, rs.len()) == Some((rs, pos + ser_records(rs).len())),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let rest = rs.drop_first();
        lemma_at_split(b, pos, ser_record(rs[0]), ser_records(rest));
        lemma_record_roundtrip(b, pos, rs[0]);
        assert(forall|i: int| 0 <= i < rest.len() ==> rest[i] == rs[i + 1]);
        lemma_records_roundtrip(b, pos + ser_record(rs[0]).len(), rest);
        assert(seq![rs[0]] + rest =~= rs);
    }
}

pub proof fn lemma_header_roundtrip(b: Seq<u8>, m: SpecMessage)
    requires
        at(b, 0, ser_header(m)),
    ensures
        parse_u16(b, 0) == Some((m.id, 2int)),
        parse_u16(b, 2) == Some((m.flags, 4int)),
        parse_u16(b, 4) == Some((m.questions.len() as u16, 6int)),
        parse_u16(b, 6) == Some((m.answers.len() as u16, 8int)),
        parse_u16(b, 8) == Some((m.authorities.len() as u16, 10int)),
        parse_u16(b, 10) == Some((m.additionals.len() as u16, 12int)),
{
    let h0 = ser_u16(m.id);
    let h1 = h0 + ser_u16(m.flags);
    let h2 = h1 + ser_u16(m.questions.len() as u16);
    let h3 = h2 + ser_u16(m.answers.len() as u16);
    let h4 = h3 + ser_u16(m.authorities.len() as u16);
    lemma_at_split(b, 0, h4, ser_u16(m.additionals.len() as u16));
    lemma_at_split(b, 0, h3, ser_u16(m.authorities.len() as u16));
    lemma_at_split(b, 0, h2, ser_u16(m.answers.len() as u16));
    lemma_at_split(b, 0, h1, ser_u16(m.questions.len() as u16));
    lemma_at_split(b, 0, h0, ser_u16(m.flags));
    lemma_u16_roundtrip(b, 0, m.id);
    lemma_u16_roundtrip(b, 2, m.flags);
    lemma_u16_roundtrip(b, 4, m.questions.len() as u16);
    lemma_u16_roundtrip(b, 6, m.answers.len() as u16);
    lemma_u16_roundtrip(b, 8, m.authorities.len() as u16);
    lemma_u16_roundtrip(b, 10, m.additionals.len() as u16);
}

/// **Round-trip theorem.** Every well-formed message survives serialization
/// followed by parsing, unchanged.
pub proof fn theorem_roundtrip(m: SpecMessage)
    requires
        valid_message(m),
    ensures
        parse_message(ser_message(m)) == Some(m),
{
    hide(parse_questions);
    hide(parse_records);
    hide(ser_questions);
    hide(ser_records);
    hide(ser_header);
    hide(parse_name);
    let b = ser_message(m);
    let h = ser_header(m);
    let q = ser_questions(m.questions);
    let an = ser_records(m.answers);
    let ns = ser_records(m.authorities);
    let ar = ser_records(m.additionals);
    lemma_at_whole(b);
    lemma_at_split(b, 0, h + q + an + ns, ar);
    lemma_at_split(b, 0, h + q + an, ns);
    lemma_at_split(b, 0, h + q, an);
    lemma_at_split(b, 0, h, q);
    lemma_header_roundtrip(b, m);
    assert(h.len() == 12) by {
        reveal(ser_header);
    }
    let p1 = 12 + q.len() as int;
    let p2 = p1 + an.len();
    let p3 = p2 + ns.len();
    lemma_questions_roundtrip(b, 12, m.questions);
    lemma_records_roundtrip(b, p1, m.answers);
    lemma_records_roundtrip(b, p2, m.authorities);
    lemma_records_roundtrip(b, p3, m.additionals);
    assert(parse_questions(b, 12, m.questions.len()) == Some((m.questions, p1)));
    assert(parse_records(b, p1, m.answers.len()) == Some((m.answers, p2)));
    assert(parse_records(b, p2, m.authorities.len()) == Some((m.authorities, p3)));
    assert(b.len() == p3 + ar.len());
}

// ---------------------------------------------------------------------------
// Parsed values are well-formed
// ---------------------------------------------------------------------------

pub proof fn lemma_parse_labels_valid(b: Seq<u8>, pos: int, seg: int)
    ensures
        parse_labels(b, pos, seg) matches Some((n, end)) ==> {
            &&& forall|i: int| 0 <= i < n.len() ==> valid_label(#[trigger] n[i])
            &&& pos < end <= b.len()
        },
    decreases seg, b.len() - pos,
{
    if !(pos < 0 || pos >= b.len() || seg < 0 || pos < seg) {
        let c = b[pos];
        if c == 0 {
        } else if c >= 192 {
            if pos + 1 < b.len() {
                let target = (c as int - 192) * 256 + b[pos + 1] as int;
                if target < seg {
                    lemma_parse_labels_valid(b, target, target);
                }
            }
        } else if c < 64 && pos + 1 + c as int <= b.len() {
            let l = b.subrange(pos + 1, pos + 1 + c as int);
            lemma_parse_labels_valid(b, pos + 1 + c as int, seg);
            if let Some((rest, end)) = parse_labels(b, pos + 1 + c as int, seg) {
                let n = seq![l] + rest;
                assert forall|i: int| 0 <= i < n.len() implies valid_label(#[trigger] n[i]) by {
                    if i > 0 {
                        assert(n[i] == rest[i - 1]);
                    }
                }
            }
        }
    }
}

pub proof fn lemma_parse_name_valid(b: Seq<u8>, pos: int)
    ensures
        parse_name(b, pos) matches Some((n, end)) ==> valid_name(n) && pos < end <= b.len(),
{
    lemma_parse_labels_valid(b, pos, pos);
}

pub proof fn lemma_parse_questions_valid(b: Seq<u8>, pos: int, n: nat)
    ensures
        parse_questions(b, pos, n) matches Some((qs, end)) ==> {
            &&& qs.len() == n
            &&& forall|i: int| 0 <= i < qs.len() ==> valid_question(#[trigger] qs[i])
        },
    decreases n,
{
    if n > 0 {
        lemma_parse_name_valid(b, pos);
        if let Some((q, p)) = parse_question(b, pos) {
            lemma_parse_questions_valid(b, p, (n - 1) as nat);
            if let Some((qs, _)) = parse_questions(b, p, (n - 1) as nat) {
                let all = seq![q] + qs;
                assert forall|i: int| 0 <= i < all.len() implies valid_question(
                    #[trigger] all[i],
                ) by {
                    if i > 0 {
                        assert(all[i] == qs[i - 1]);
                    }
                }
            }
        }
    }
}

pub proof fn lemma_parse_record_valid(b: Seq<u8>, pos: int)
    ensures
        parse_record(b, pos) matches Some((r, end)) ==> valid_record(r) && pos < end <= b.len(),
{
    lemma_parse_name_valid(b, pos);
    if let Some((r, end)) = parse_record(b, pos) {
        let p1 = parse_name(b, pos).unwrap().1;
        let rdlen = parse_u16(b, p1 + 8).unwrap().0;
        lemma_canon_rdata_idem(b, r.rtype, p1 + 10, p1 + 10 + rdlen as int);
    }
}

pub proof fn lemma_parse_records_valid(b: Seq<u8>, pos: int, n: nat)
    ensures
        parse_records(b, pos, n) matches Some((rs, end)) ==> {
            &&& rs.len() == n
            &&& forall|i: int| 0 <= i < rs.len() ==> valid_record(#[trigger] rs[i])
        },
    decreases n,
{
    if n > 0 {
        lemma_parse_record_valid(b, pos);
        if let Some((r, p)) = parse_record(b, pos) {
            lemma_parse_records_valid(b, p, (n - 1) as nat);
            if let Some((rs, _)) = parse_records(b, p, (n - 1) as nat) {
                let all = seq![r] + rs;
                assert forall|i: int| 0 <= i < all.len() implies valid_record(#[trigger] all[i]) by {
                    if i > 0 {
                        assert(all[i] == rs[i - 1]);
                    }
                }
            }
        }
    }
}

/// Every message the parser accepts is well-formed.
pub proof fn theorem_parse_valid(b: Seq<u8>)
    ensures
        parse_message(b) matches Some(m) ==> valid_message(m),
{
    if b.len() >= HEADER_LEN {
        let qd = parse_u16(b, 4).unwrap().0;
        let an = parse_u16(b, 6).unwrap().0;
        let ns = parse_u16(b, 8).unwrap().0;
        let ar = parse_u16(b, 10).unwrap().0;
        lemma_parse_questions_valid(b, 12, qd as nat);
        if let Some((_, p1)) = parse_questions(b, 12, qd as nat) {
            lemma_parse_records_valid(b, p1, an as nat);
            if let Some((_, p2)) = parse_records(b, p1, an as nat) {
                lemma_parse_records_valid(b, p2, ns as nat);
                if let Some((_, p3)) = parse_records(b, p2, ns as nat) {
                    lemma_parse_records_valid(b, p3, ar as nat);
                }
            }
        }
    }
}

/// **Canonicalization theorem.** Compression makes parsing many-to-one, so
/// `serialize(parse(b)) == b` cannot hold. What does hold: re-serializing a
/// parsed message (uncompressed) and parsing again gives the same message.
pub proof fn theorem_reserialize_stable(b: Seq<u8>)
    ensures
        parse_message(b) matches Some(m) ==> parse_message(ser_message(m)) == Some(m),
{
    theorem_parse_valid(b);
    if let Some(m) = parse_message(b) {
        theorem_roundtrip(m);
    }
}

// ---------------------------------------------------------------------------
// Size bounds: each question and record consumes a minimum number of bytes
// ---------------------------------------------------------------------------

pub proof fn lemma_parse_questions_progress(b: Seq<u8>, pos: int, n: nat)
    ensures
        parse_questions(b, pos, n) matches Some((qs, end)) ==> pos + 5 * n <= end <= b.len()
            || (n == 0 && end == pos),
    decreases n,
{
    if n > 0 {
        lemma_parse_name_valid(b, pos);
        if let Some((q, p)) = parse_question(b, pos) {
            lemma_parse_questions_progress(b, p, (n - 1) as nat);
        }
    }
}

pub proof fn lemma_parse_records_progress(b: Seq<u8>, pos: int, n: nat)
    ensures
        parse_records(b, pos, n) matches Some((rs, end)) ==> pos + 11 * n <= end <= b.len()
            || (n == 0 && end == pos),
    decreases n,
{
    if n > 0 {
        lemma_parse_name_valid(b, pos);
        if let Some((r, p)) = parse_record(b, pos) {
            lemma_parse_records_progress(b, p, (n - 1) as nat);
        }
    }
}

/// Any message `parse_message` accepts has counts that fit its size, so the
/// exec parser's up-front count check never rejects a valid message.
pub proof fn lemma_counts_fit(b: Seq<u8>)
    ensures
        parse_message(b) is Some ==> {
            let qd = parse_u16(b, 4).unwrap().0 as int;
            let rr = parse_u16(b, 6).unwrap().0 as int + parse_u16(b, 8).unwrap().0 as int
                + parse_u16(b, 10).unwrap().0 as int;
            5 * qd + 11 * rr <= b.len() - 12
        },
{
    if b.len() >= HEADER_LEN {
        let qd = parse_u16(b, 4).unwrap().0;
        let an = parse_u16(b, 6).unwrap().0;
        let ns = parse_u16(b, 8).unwrap().0;
        let ar = parse_u16(b, 10).unwrap().0;
        lemma_parse_questions_progress(b, 12, qd as nat);
        if let Some((_, p1)) = parse_questions(b, 12, qd as nat) {
            lemma_parse_records_progress(b, p1, an as nat);
            if let Some((_, p2)) = parse_records(b, p1, an as nat) {
                lemma_parse_records_progress(b, p2, ns as nat);
                if let Some((_, p3)) = parse_records(b, p2, ns as nat) {
                    lemma_parse_records_progress(b, p3, ar as nat);
                }
            }
        }
    }
}

} // verus!
