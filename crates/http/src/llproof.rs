//! What the llhttp drop-in's head decisions (`llcore.rs`) amount to.
//!
//! - `theorem_ll_request` and `theorem_ll_response`: a head the adapter
//!   accepts as HTTP/1.0 or 1.1 is, byte for byte on the wire, a head the
//!   spec accepts, with the head end and framing the adapter reports; and
//!   every recipient in the model of `rfc.rs` reads that same head end and
//!   framing, or rejects the message.
//! - `theorem_ll_request_other` and `theorem_ll_response_other`: a head
//!   the adapter accepts as HTTP/0.9 or HTTP/2.0 (llhttp takes these;
//!   the machine checks them as HTTP/1.0 heads) is accepted by no
//!   recipient in the model. So no recipient can read it another way.
//!
//! Together: whatever head the drop-in reports, no recipient in the model
//! frames the same bytes differently.
use crate::framing::*;
use crate::llcore::*;
use crate::rfc::*;
use crate::spec::*;
use crate::stream::*;
use crate::stream_proof::*;
use crate::unique::*;
use crate::unique_chunked::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// HTTP/1.x: the adapter's run is the machine's
// ---------------------------------------------------------------------------

/// A run that ends with `ver == VER_1X` started with it, and every step
/// of it was the machine's step on the wire byte itself.
pub proof fn lemma_v1(s: LS, w: Seq<u8>, j: int)
    requires
        0 <= j <= w.len(),
        lr(s, w, j) matches Some((t, _)) && t.ver == VER_1X,
    ensures
        s.ver == VER_1X,
        hr(s.hs, w, j) == Some((lr(s, w, j)->Some_0.0.hs, lr(s, w, j)->Some_0.1)),
    decreases w.len() - j,
{
    if j < w.len() && !(s.hs.ph is Done) {
        let c = w[j];
        let s2 = lstep(s, c)->Some_0;
        lemma_v1(s2, w, j + 1);
        if s.hs.ph == Ph::Target && c == CR {
            let t = l09(s)->Some_0;
            assert(ver_byte(t.hs.ph, t.ver, c) == Some((c, t.ver)));
            assert(false);
        }
        assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, VER_1X)));
        assert(hstep(s.hs, c) == Some(s2.hs));
    }
}

/// Requests accepted as HTTP/1.x.
pub proof fn theorem_ll_request(w: Seq<u8>, max: nat, c: Recipient)
    requires
        lr(lstart(true), w, 0) matches Some((t, _)) && t.hs.ph is Done && t.ver == VER_1X,
        max >= w.len(),
    ensures
        ({
            let (t, k) = lr(lstart(true), w, 0)->Some_0;
            let body = request_framing_x(t.hs.f, t.hs.minor);
            &&& parse_request(w, max) matches Parsed::Done(r, end) && end == k && r.minor == t.hs.minor
            &&& body is Some
            &&& (read_request(w, c) == (Reading::Accept { head: k, framing: as_framing(body->Some_0) })
                || read_request(w, c) is Reject)
        }),
{
    let s0 = lstart(true);
    lemma_v1(s0, w, 0);
    lemma_hr(s0.hs, w, 0);
    assert(sfx(w, 0) =~= w);
    theorem_stream_request(w, max, false);
    theorem_request_unique_framing(w, max, c);
}

/// Responses accepted as HTTP/1.x, to a HEAD request (`head_req`) or not.
pub proof fn theorem_ll_response(w: Seq<u8>, max: nat, head_req: bool, c: Recipient)
    requires
        lr(lstart(false), w, 0) matches Some((t, _)) && t.hs.ph is Done && t.ver == VER_1X,
        max >= w.len(),
    ensures
        ({
            let (t, k) = lr(lstart(false), w, 0)->Some_0;
            let body = response_framing_x(t.hs.f, t.hs.minor, t.hs.status, head_req, false);
            &&& parse_response(w, max) matches Parsed::Done(r, end) && end == k && r.minor == t.hs.minor
            &&& body is Some
            &&& (read_response(w, head_req, false, c) == (Reading::Accept {
                head: k,
                framing: as_framing(body->Some_0),
            }) || read_response(w, head_req, false, c) is Reject)
        }),
{
    let s0 = lstart(false);
    lemma_v1(s0, w, 0);
    lemma_hr(s0.hs, w, 0);
    assert(sfx(w, 0) =~= w);
    theorem_stream_response(w, max, head_req, false);
    theorem_response_unique(w, max, head_req, false, c);
}

// ---------------------------------------------------------------------------
// Other versions, requests: the request line as every recipient reads it
// ---------------------------------------------------------------------------

/// Positions in the request line, found as the run passes them.
pub struct Pos {
    /// Where the request line starts, after any empty lines.
    pub a: int,
    /// The SP after the method.
    pub me: int,
    /// The SP after the target.
    pub te: int,
    /// The CR that ends the line.
    pub e: int,
    /// The last SP of the line.
    pub q: int,
    /// A byte of the target that rules it out as an HTTP/1.x version.
    pub mm: int,
}

/// `w[..j]` is a run of empty lines (CRLF).
pub open spec fn emp(w: Seq<u8>, j: int) -> bool
    decreases j,
{
    j == 0 || (j >= 2 && w[j - 2] == CR && w[j - 1] == LF && emp(w, j - 2))
}

/// A byte that every recipient takes as part of a word: not a line end,
/// and not one of the separators of `rfc::is_sep`.
pub open spec fn wordb(x: u8) -> bool {
    x != CR && x != LF && x != SP && x != HTAB && x != 0x0B && x != 0x0C
}

pub open spec fn words(w: Seq<u8>, lo: int, hi: int) -> bool {
    forall|i: int| lo <= i < hi ==> wordb(#[trigger] w[i])
}

/// Byte `i` of an HTTP/1.x version.
pub open spec fn pat(i: int, x: u8) -> bool {
    if 0 <= i < 7 {
        x == http1_prefix()[i]
    } else {
        is_digit(x)
    }
}

/// The request line of `w` ends at `p.e`, and its last word is not an
/// HTTP/1.x version.
pub open spec fn other_line(w: Seq<u8>, p: Pos) -> bool {
    &&& 0 <= p.a < p.q && p.q + 1 < p.e
    &&& emp(w, p.a)
    &&& clean(w, p.a, p.e)
    &&& w[p.e] == CR
    &&& w[p.q] == SP
    &&& words(w, p.q + 1, p.e)
    &&& version_word(w.subrange(p.q + 1, p.e)) is None
}

/// What is known of `w[..j]` when the adapter is in state `s` there.
pub open spec fn rinv(w: Seq<u8>, j: int, s: LS, p: Pos) -> bool {
    &&& 0 <= j <= w.len()
    &&& s.hs.req
    &&& match s.hs.ph {
        Ph::RStart => emp(w, j) && s.ver == VER_1X,
        Ph::RStartLf => j >= 1 && emp(w, j - 1) && w[j - 1] == CR && s.ver == VER_1X,
        Ph::Method => 0 <= p.a < j && emp(w, p.a) && words(w, p.a, j) && s.ver == VER_1X,
        Ph::Target0 => 0 <= p.a < p.me && p.me == j - 1 && emp(w, p.a) && words(w, p.a, p.me) && w[p.me] == SP
            && s.ver == VER_1X,
        Ph::Target => {
            let n = j - p.me - 1;
            &&& 0 <= p.a < p.me && p.me + 1 < j && emp(w, p.a) && words(w, p.a, p.me) && w[p.me] == SP
            &&& words(w, p.me + 1, j)
            &&& s.ver == VER_1X
            &&& s.tv <= 8 ==> n == s.tv
            &&& s.tv > 8 ==> n > 8 || (0 <= p.mm < n && p.mm < 8 && !pat(p.mm, w[p.me + 1 + p.mm]))
        },
        Ph::RVer { k } => {
            &&& 0 <= p.a < p.me && p.me + 1 < p.te && p.te == j - 1 - k && emp(w, p.a) && words(w, p.a, p.me)
                && w[p.me] == SP
            &&& words(w, p.me + 1, p.te)
            &&& w[p.te] == SP
            &&& words(w, p.te + 1, j)
            &&& k <= 7
            &&& k <= 5 ==> s.ver == VER_1X
            &&& k > 5 ==> s.ver == VER_1X || w[p.te + 6] != 0x31
        },
        Ph::RCr => {
            &&& 0 <= p.a < p.me && p.me + 1 < p.te && p.te == j - 9 && emp(w, p.a) && words(w, p.a, p.me) && w[p.me]
                == SP
            &&& words(w, p.me + 1, p.te)
            &&& w[p.te] == SP
            &&& words(w, p.te + 1, j)
            &&& s.ver == VER_1X || w[p.te + 6] != 0x31
        },
        Ph::RLf => j == p.e + 1 && (s.ver != VER_1X ==> other_line(w, p)),
        Ph::Line | Ph::EndLf | Ph::Name { .. } | Ph::Val { .. } | Ph::ValLf { .. } | Ph::Done => p.e + 2 <= j
            && w[p.e + 1] == LF && (s.ver != VER_1X ==> other_line(w, p)),
        _ => false,
    }
}

/// The positions after the step on `w[j]`.
pub open spec fn next_pos(w: Seq<u8>, j: int, s: LS, p: Pos) -> Pos {
    let c = w[j];
    match s.hs.ph {
        Ph::RStart => Pos { a: j, ..p },
        Ph::Method => Pos { me: j, ..p },
        Ph::Target0 => Pos { mm: 0, ..p },
        Ph::Target => if c == SP {
            Pos { te: j, ..p }
        } else if c == CR {
            Pos { e: j, q: p.me, ..p }
        } else if s.tv <= 7 {
            Pos { mm: j - p.me - 1, ..p }
        } else {
            p
        },
        Ph::RCr => Pos { e: j, q: p.te, ..p },
        _ => p,
    }
}

/// A target that `tv` does not count as a version is not one.
proof fn lemma_target_not_version(w: Seq<u8>, me: int, e: int, tv: u8, mm: int)
    requires
        0 <= me,
        me + 1 < e <= w.len(),
        tv != 8,
        tv <= 8 ==> e - me - 1 == tv,
        tv > 8 ==> e - me - 1 > 8 || (0 <= mm < e - me - 1 && mm < 8 && !pat(mm, w[me + 1 + mm])),
    ensures
        version_word(w.subrange(me + 1, e)) is None,
{
    let x = w.subrange(me + 1, e);
    if x.len() == 8 {
        assert(tv > 8);
        assert(x[mm] == w[me + 1 + mm]);
        if mm < 7 {
            assert(x.subrange(0, 7)[mm] == x[mm]);
        }
    }
}

/// A version whose major digit is not `1` is not an HTTP/1.x version.
proof fn lemma_version_not_1(w: Seq<u8>, te: int)
    requires
        0 <= te,
        te + 9 <= w.len(),
        w[te + 6] != 0x31,
    ensures
        version_word(w.subrange(te + 1, te + 9)) is None,
{
    let x = w.subrange(te + 1, te + 9);
    assert(x.subrange(0, 7)[5] == x[5]);
    assert(x[5] == w[te + 6]);
    assert(http1_prefix()[5] == 0x31);
}

/// The invariant holds along the run; at the end, with a version other
/// than 1.x, it gives the request line.
proof fn lemma_request_run(w: Seq<u8>, j: int, s: LS, p: Pos) -> (r: Pos)
    requires
        rinv(w, j, s, p),
        lr(s, w, j) matches Some((t, _)) && t.hs.ph is Done && t.ver != VER_1X,
    ensures
        other_line(w, r),
        r.e + 1 < w.len(),
        w[r.e + 1] == LF,
    decreases w.len() - j,
{
    if s.hs.ph is Done {
        return p;
    }
    let c = w[j];
    let s2 = lstep(s, c)->Some_0;
    let p2 = next_pos(w, j, s, p);
    assert(rinv(w, j + 1, s2, p2)) by {
        lemma_request_step(w, j, s, p);
    }
    lemma_request_run(w, j + 1, s2, p2)
}

/// One step keeps the invariant.
proof fn lemma_request_step(w: Seq<u8>, j: int, s: LS, p: Pos)
    requires
        rinv(w, j, s, p),
        0 <= j < w.len(),
        lstep(s, w[j]) is Some,
    ensures
        rinv(w, j + 1, lstep(s, w[j])->Some_0, next_pos(w, j, s, p)),
{
    let c = w[j];
    let s2 = lstep(s, c)->Some_0;
    let p2 = next_pos(w, j, s, p);
    match s.hs.ph {
        Ph::RStart => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
            if c != CR {
                assert(is_tchar(c));
                assert(wordb(c));
            }
        },
        Ph::RStartLf => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
            assert(emp(w, j + 1));
        },
        Ph::Method => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
            if c != SP {
                assert(is_tchar(c));
                assert(wordb(c));
            }
        },
        Ph::Target0 => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
            assert(is_target_char(c));
            assert(wordb(c));
            assert(s2.tv == tv_next(0, c));
            if s2.tv > 8 {
                assert(!pat(0, c));
            }
        },
        Ph::Target => {
            if c == CR {
                let t = l09(s)->Some_0;
                assert(ver_byte(t.hs.ph, t.ver, c) == Some((c, t.ver)));
                assert(s2.hs.ph == Ph::RLf);
                lemma_target_not_version(w, p.me, j, s.tv, p.mm);
                assert(clean(w, p.a, j));
            } else {
                assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
                if c != SP {
                    assert(is_target_char(c));
                    assert(wordb(c));
                    assert(s2.tv == tv_next(s.tv, c));
                    let n = j - p.me - 1;
                    if s.tv <= 7 && s2.tv > 8 {
                        assert(!pat(n, c));
                    }
                }
            }
        },
        Ph::RVer { k } => {
            let (m, v) = ver_byte(s.hs.ph, s.ver, c)->Some_0;
            assert(hstep(s.hs, m) == Some(s2.hs));
            if k < 7 {
                assert(m == http1_prefix()[k as int]);
                assert(wordb(c));
            } else {
                assert(is_digit(m));
                assert(wordb(c));
            }
        },
        Ph::RCr => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
            assert(c == CR);
            if s.ver != VER_1X {
                lemma_version_not_1(w, p.te);
                assert(clean(w, p.a, j));
            }
        },
        Ph::RLf => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
        },
        _ => {
            assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
            assert(hstep(s.hs, c) == Some(s2.hs));
        },
    }
}

/// `emp`, read forwards from `i`.
spec fn empf(w: Seq<u8>, i: int, a: int) -> bool
    decreases a - i,
{
    i == a || (i + 2 <= a && w[i] == CR && w[i + 1] == LF && empf(w, i + 2, a))
}

proof fn lemma_empf_push(w: Seq<u8>, i: int, a: int)
    requires
        0 <= i <= a,
        a + 1 < w.len(),
        empf(w, i, a),
        w[a] == CR,
        w[a + 1] == LF,
    ensures
        empf(w, i, a + 2),
    decreases a - i,
{
    if i < a {
        lemma_empf_push(w, i + 2, a);
    } else {
        assert(empf(w, a + 2, a + 2));
    }
}

proof fn lemma_emp_empf(w: Seq<u8>, a: int)
    requires
        0 <= a < w.len(),
        emp(w, a),
    ensures
        empf(w, 0, a),
    decreases a,
{
    if a > 0 {
        lemma_emp_empf(w, a - 2);
        lemma_empf_push(w, 0, a - 2);
    }
}

proof fn lemma_empf_skip(w: Seq<u8>, i: int, a: int)
    requires
        0 <= i <= a < w.len(),
        empf(w, i, a),
        w[a] != CR,
    ensures
        skip_empty_lines(w, i) == Parsed::Done((), a),
    decreases a - i,
{
    if i < a {
        lemma_empf_skip(w, i + 2, a);
    }
}

/// No recipient accepts a request whose request line ends in a word that
/// is not an HTTP/1.x version.
proof fn lemma_request_rejected(w: Seq<u8>, p: Pos, c: Recipient)
    requires
        other_line(w, p),
        p.e + 1 < w.len(),
        w[p.e + 1] == LF,
    ensures
        !(read_request(w, c) is Accept),
{
    let (a, q, e) = (p.a, p.q, p.e);
    lemma_emp_empf(w, a);
    lemma_empf_skip(w, 0, a);
    lemma_read_clean(w, a, e, c);
    let l = w.subrange(a, e);
    assert(l.len() > 0);
    lemma_skip(w, 0, c, c.empty_lines, l, e + 2);
    let p0 = skip_empty(w, 0, c, c.empty_lines)->Done_1;
    // The version is the last word, whatever the recipient splits on.
    assert(l.last() == w[e - 1]);
    assert(wordb(w[e - 1]));
    let tt = if c.ws_start_line {
        rtrim_sep(l, c)
    } else {
        l
    };
    assert(tt == l);
    assert forall|m: int| q - a < m < l.len() implies !is_sep(c, #[trigger] l[m]) by {
        assert(l[m] == w[a + m]);
        assert(wordb(w[a + m]));
    }
    assert(l[q - a] == w[q]);
    lemma_last_sep(l, l.len() as int, q - a, c);
    assert(l.subrange(q - a + 1, l.len() as int) =~= w.subrange(q + 1, e));
    assert(request_version(l, c) is None);
    if p0 < a {
        assert(read_lines(w, p0, c) == Parsed::Done(Seq::<Seq<u8>>::empty(), p0 + 2));
    } else {
        match read_lines(w, e + 2, c) {
            Parsed::Done(ls, e2) => {
                assert(read_lines(w, a, c) == Parsed::Done(seq![l] + ls, e2));
                assert((seq![l] + ls)[0] == l);
            },
            _ => {},
        }
    }
}

/// Requests accepted as HTTP/0.9 or HTTP/2.0: no recipient in the model
/// accepts them, so none reads them another way.
pub proof fn theorem_ll_request_other(w: Seq<u8>, c: Recipient)
    requires
        lr(lstart(true), w, 0) matches Some((t, _)) && t.hs.ph is Done && t.ver != VER_1X,
    ensures
        !(read_request(w, c) is Accept),
{
    let p0 = Pos { a: 0, me: 0, te: 0, e: 0, q: 0, mm: 0 };
    let p = lemma_request_run(w, 0, lstart(true), p0);
    lemma_request_rejected(w, p, c);
}

// ---------------------------------------------------------------------------
// Other versions, responses
// ---------------------------------------------------------------------------

/// What is known of `w[..j]` in a response head.
pub open spec fn sinv(w: Seq<u8>, j: int, s: LS) -> bool {
    &&& 0 <= j <= w.len()
    &&& !s.hs.req
    &&& match s.hs.ph {
        Ph::SVer { k } => j == k && k <= 7 && (k > 0 ==> w[0] == 0x48) && (k <= 5 ==> s.ver == VER_1X) && (k > 5
            ==> s.ver == VER_1X || w[5] == 0x30 || w[5] == 0x32),
        Ph::SSp | Ph::Code { .. } | Ph::Reason | Ph::SLf | Ph::Line | Ph::EndLf | Ph::Name { .. } | Ph::Val { .. }
        | Ph::ValLf { .. } | Ph::Done => j >= 8 && w[0] == 0x48 && (s.ver == VER_1X || w[5] == 0x30 || w[5]
            == 0x32),
        _ => false,
    }
}

proof fn lemma_response_run(w: Seq<u8>, j: int, s: LS)
    requires
        sinv(w, j, s),
        lr(s, w, j) matches Some((t, _)) && t.hs.ph is Done && t.ver != VER_1X,
    ensures
        w.len() >= 8,
        w[0] == 0x48,
        w[5] == 0x30 || w[5] == 0x32,
    decreases w.len() - j,
{
    if s.hs.ph is Done {
        return ;
    }
    let c = w[j];
    let s2 = lstep(s, c)->Some_0;
    assert(sinv(w, j + 1, s2)) by {
        match s.hs.ph {
            Ph::SVer { k } => {
                let (m, v) = ver_byte(s.hs.ph, s.ver, c)->Some_0;
                assert(hstep(s.hs, m) == Some(s2.hs));
                if k == 0 {
                    assert(m == http1_prefix()[0]);
                }
            },
            _ => {
                assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, s.ver)));
                assert(hstep(s.hs, c) == Some(s2.hs));
            },
        }
    }
    lemma_response_run(w, j + 1, s2);
}

proof fn lemma_find_eol_ge(b: Seq<u8>, i: int, c: Recipient)
    requires
        0 <= i <= b.len(),
    ensures
        i <= find_eol(b, i, c) <= b.len(),
    decreases b.len() - i,
{
    if i < b.len() && !is_eol(b, i, c) {
        lemma_find_eol_ge(b, i + 1, c);
    }
}

/// No recipient accepts a response whose status line starts with a
/// version other than HTTP/1.x.
proof fn lemma_response_rejected(w: Seq<u8>, head_req: bool, connect: bool, c: Recipient)
    requires
        w.len() >= 8,
        w[0] == 0x48,
        w[5] == 0x30 || w[5] == 0x32,
    ensures
        !(read_response(w, head_req, connect, c) is Accept),
{
    assert(!is_eol(w, 0, c));
    lemma_find_eol_ge(w, 1, c);
    let j = find_eol(w, 0, c);
    assert(j == find_eol(w, 1, c));
    match read_line(w, 0, c) {
        Parsed::Done(l, n) => {
            // The line starts with `w[0]`, so it is not empty, and its
            // sixth byte is `w[5]` if it has one.
            let raw = if w[j] == CR {
                w.subrange(0, j)
            } else if j > 0 && w[j - 1] == CR {
                w.subrange(0, j - 1)
            } else {
                w.subrange(0, j)
            };
            assert(raw.len() >= 1) by {
                if j == 1 && w[0] == CR {
                }
            }
            assert(l == raw || l == replace(raw, CR, SP));
            assert(l.len() == raw.len());
            assert(skip_empty(w, 0, c, c.empty_lines) == Parsed::Done((), 0));
            if l.len() >= 12 {
                assert(raw[5] == w[5]);
                assert(l[5] == w[5]);
                assert(l.subrange(0, 8).subrange(0, 7)[5] == l[5]);
                assert(http1_prefix()[5] == 0x31);
                assert(version_word(l.subrange(0, 8)) is None);
            }
            assert(status_line(l, c) is None);
            if n > 0 {
                match read_lines(w, n, c) {
                    Parsed::Done(ls, e2) => {
                        assert(read_lines(w, 0, c) == Parsed::Done(seq![l] + ls, e2));
                        assert((seq![l] + ls)[0] == l);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

/// Responses accepted as HTTP/0.9 or HTTP/2.0: no recipient in the model
/// accepts them.
pub proof fn theorem_ll_response_other(w: Seq<u8>, head_req: bool, connect: bool, c: Recipient)
    requires
        lr(lstart(false), w, 0) matches Some((t, _)) && t.hs.ph is Done && t.ver != VER_1X,
    ensures
        !(read_response(w, head_req, connect, c) is Accept),
{
    lemma_response_run(w, 0, lstart(false));
    lemma_response_rejected(w, head_req, connect, c);
}

// ---------------------------------------------------------------------------
// The one-shot path: a machine run is an adapter run
// ---------------------------------------------------------------------------

/// The phases after the version.
pub open spec fn past_version(ph: Ph) -> bool {
    !(ph is RStart || ph is RStartLf || ph is Method || ph is Target0 || ph is Target || ph is RVer || ph is SVer)
}

/// A run keeps `req` and `host`; after the version it keeps `minor`; and
/// outside a status line it keeps `status`.
pub proof fn lemma_hr_frame(s: HS, w: Seq<u8>, j: int)
    requires
        0 <= j <= w.len(),
        hr(s, w, j) is Some,
    ensures
        ({
            let t = hr(s, w, j)->Some_0.0;
            &&& t.req == s.req
            &&& t.host == s.host
            &&& past_version(s.ph) ==> t.minor == s.minor
            &&& (s.req && !(s.ph is SVer || s.ph is SSp || s.ph is Code)) ==> t.status == s.status
            &&& (past_version(s.ph) && !(s.ph is SSp || s.ph is Code)) ==> t.status == s.status
        }),
    decreases w.len() - j,
{
    if j < w.len() && !(s.ph is Done) {
        let s2 = hstep(s, w[j])->Some_0;
        lemma_hr_frame(s2, w, j + 1);
    }
}

/// A machine run to an HTTP/1.0 or 1.1 head is the adapter's run.
pub proof fn lemma_v1_conv(s: LS, w: Seq<u8>, j: int)
    requires
        0 <= j <= w.len(),
        s.ver == VER_1X,
        hr(s.hs, w, j) matches Some((t, _)) && t.minor <= 1,
    ensures
        lr(s, w, j) matches Some((u, e)) && u.hs == hr(s.hs, w, j)->Some_0.0 && u.ver == VER_1X && e == hr(
            s.hs,
            w,
            j,
        )->Some_0.1,
    decreases w.len() - j,
{
    if j < w.len() && !(s.hs.ph is Done) {
        let c = w[j];
        let h = hstep(s.hs, c)->Some_0;
        if is_ver_phase(s.hs.ph) && ver_k(s.hs.ph) == 7 {
            lemma_hr_frame(h, w, j + 1);
            assert(h.minor == (c - 0x30) as u8);
        }
        assert(ver_byte(s.hs.ph, s.ver, c) == Some((c, VER_1X)));
        let s2 = lstep(s, c)->Some_0;
        assert(s2.hs == h);
        lemma_v1_conv(s2, w, j + 1);
    }
}

/// A head within one limit on field lines is the same head within a
/// larger one.
pub proof fn lemma_headers_more(b: Seq<u8>, i: int, max: nat, max2: nat)
    requires
        parse_headers(b, i, max) is Done,
        max <= max2,
    ensures
        parse_headers(b, i, max2) == parse_headers(b, i, max),
    decreases b.len() - i,
{
    if 0 <= i < b.len() && b[i] != CR {
        let n = parse_header(b, i)->Done_1;
        lemma_headers_more(b, n, (max - 1) as nat, (max2 - 1) as nat);
    }
}

/// The state the one-shot path builds for a request head is the state
/// the adapter's run ends in.
pub proof fn lemma_fast_request(w: Seq<u8>, max: nat, done: HS)
    requires
        hrun(request_start_with(false), w) matches Some((t, _)) && t.ph is Done,
        parse_request(w, max) matches Parsed::Done(q, _) && q.minor == done.minor && (fields_of(w, q.headers) matches Some(
            g,
        ) && fields_agree(done.f, g)),
        done.ph is Done,
        done.minor <= 1,
        done.status == 0,
        done.req,
        !done.host,
    ensures
        lr(lstart(true), w, 0) matches Some((u, e)) && u.hs == done && u.ver == VER_1X && e == parse_request(
            w,
            max,
        )->Done_1,
{
    let s0 = request_start_with(false);
    let mx = if max >= w.len() {
        max
    } else {
        w.len()
    };
    let h2 = lit(
        w,
        parse_version(
            w,
            run_then(w, run_then(w, skip_empty_lines(w, 0)->Done_1, Cls::Token, SP)->Done_1, Cls::Target, SP)->Done_1,
        )->Done_1,
        crlf(),
    )->Done_1;
    lemma_headers_more(w, h2, max, mx);
    assert(parse_request(w, mx) == parse_request(w, max));
    theorem_stream_request(w, mx, false);
    lemma_hr(s0, w, 0);
    assert(sfx(w, 0) =~= w);
    lemma_hr_frame(s0, w, 0);
    let t = hrun(s0, w)->Some_0.0;
    assert(t.f == done.f);
    assert(t == done);
    lemma_v1_conv(lstart(true), w, 0);
}

/// The same for a response head.
pub proof fn lemma_fast_response(w: Seq<u8>, max: nat, done: HS)
    requires
        hrun(response_start(), w) matches Some((t, _)) && t.ph is Done,
        parse_response(w, max) matches Parsed::Done(q, _) && q.minor == done.minor && q.status == done.status && (
        fields_of(w, q.headers) matches Some(g) && fields_agree(done.f, g)),
        done.ph is Done,
        done.minor <= 1,
        !done.req,
        !done.host,
    ensures
        lr(lstart(false), w, 0) matches Some((u, e)) && u.hs == done && u.ver == VER_1X && e == parse_response(
            w,
            max,
        )->Done_1,
{
    let s0 = response_start();
    let mx = if max >= w.len() {
        max
    } else {
        w.len()
    };
    lemma_headers_more(w, parse_status_line(w, 0)->Done_1, max, mx);
    assert(parse_response(w, mx) == parse_response(w, max));
    theorem_stream_response(w, mx, false, false);
    lemma_hr(s0, w, 0);
    assert(sfx(w, 0) =~= w);
    lemma_hr_frame(s0, w, 0);
    let t = hrun(s0, w)->Some_0.0;
    assert(t.f == done.f);
    assert(t == done);
    lemma_v1_conv(lstart(false), w, 0);
}

} // verus!
