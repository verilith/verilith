//! Field sections (RFC 9204 §4.5): the verified decoder of one section,
//! and the decoder's handling of blocked streams and acknowledgments
//! around it (`Decoder::decode`).
use crate::decoder::*;
use crate::fields::*;
use crate::integer::{self, IntE};
use crate::spec::*;
use crate::strings::{self, StrE};
use crate::table::*;
use verilith_hpack::huffman;
use vstd::prelude::*;

verus! {

/// What decoding a field section gave (`spec::Decoded`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Res {
    /// The field lines are in the output.
    Done,
    /// The stream is blocked: decode the same section again once
    /// `feed_encoder` reports the stream.
    Blocked,
    /// Over SETTINGS_MAX_FIELD_SECTION_SIZE; the decoder is unchanged.
    TooBig,
    /// QPACK_DECOMPRESSION_FAILED (a connection error).
    Bad,
}

pub enum LineE {
    Bad,
    TooBig,
    /// The end of the representation, and the field line's size.
    Ok(usize, u64),
}

/// Required Insert Count from its encoding (`spec::decode_ric`).
pub fn decode_ric_x(enc: u64, mc: u64, total: u64) -> (r: Option<u64>)
    requires
        enc <= MAX_INT,
        mc <= CAP_LIMIT,
        total <= MAX_INT,
    ensures
        match decode_ric(enc as nat, mc as nat, total as nat) {
            Some(v) => r == Some(v as u64) && v <= MAX_INT + CAP_LIMIT,
            None => r is None,
        },
{
    let me = mc / 32;
    let full = 2 * me;
    if enc == 0 {
        return Some(0);
    }
    if enc > full {
        return None;
    }
    let max_value = total + me;
    let q = max_value / full;
    proof {
        assert(q * full <= max_value) by (nonlinear_arith)
            requires
                q == max_value / full,
                full > 0,
        ;
    }
    let max_wrapped = q * full;
    let ric = max_wrapped + enc - 1;
    if ric > max_value {
        if ric <= full {
            None
        } else {
            Some(ric - full)
        }
    } else if ric == 0 {
        None
    } else {
        Some(ric)
    }
}

/// The dynamic entry a relative index refers to in a field line, if valid.
#[inline(always)]
fn dref_rel(t: &DynTable, ric: u64, base: u64, i: u64) -> (r: Option<u64>)
    requires
        t.inv(),
    ensures
        match r {
            Some(a) => a == base - 1 - i && dref_ok(t.view(), ric as nat, base - 1 - i),
            None => !dref_ok(t.view(), ric as nat, base - 1 - i),
        },
{
    if i >= base {
        return None;
    }
    let a = base - 1 - i;
    if a < ric && a >= t.dropped && a < t.icount() {
        Some(a)
    } else {
        None
    }
}

/// The same for a post-base index.
#[inline(always)]
fn dref_post(t: &DynTable, ric: u64, base: u64, i: u64) -> (r: Option<u64>)
    requires
        t.inv(),
    ensures
        match r {
            Some(a) => a == base + i && dref_ok(t.view(), ric as nat, (base + i) as int),
            None => !dref_ok(t.view(), ric as nat, (base + i) as int),
        },
{
    if i >= ric || base >= ric - i {
        return None;
    }
    let a = base + i;
    if a >= t.dropped && a < t.icount() {
        Some(a)
    } else {
        None
    }
}

/// Decodes the field line representation at `b[pos]` (`spec::line`) and
/// appends it to `out` if its size is within `budget`. The second result is
/// the work: strings decoded, bytes copied, one step for the call.
pub fn line_x(
    t: &DynTable,
    ric: u64,
    base: u64,
    b: &[u8],
    pos: usize,
    budget: u64,
    out: &mut Fields,
    s1: &mut Vec<u8>,
    s2: &mut Vec<u8>,
    dt: &[u32],
) -> (r: (LineE, Ghost<nat>))
    requires
        t.inv(),
        ric <= icount(t.view()),
        old(out).inv(),
        pos < b@.len(),
        b@.len() <= 0x1000_0000,
        huffman::layout_ok(),
        huffman::dtab_ok(dt@),
    ensures
        final(out).inv(),
        match line(t.view(), ric as nat, base as nat, b@, pos as int) {
            None => r.0 is Bad,
            Some((f, e)) => pos < e <= b@.len() && if fsize(f) > budget {
                r.0 is TooBig
            } else {
                &&& r.0 == LineE::Ok(e as usize, fsize(f) as u64)
                &&& final(out).view() == old(out).view().push(f)
                &&& pos < e <= b@.len()
                &&& r.1@ <= 4 * (e - pos) + 9 + fsize(f)
            },
        },
{
    proof {
        reveal(line);
    }
    let c = b[pos];
    let lim = b.len() as u64;
    if c >= 0x80 {
        match integer::decode(b, pos, 6) {
            IntE::Ok(i, e) => {
                if c >= 0xC0 {
                    if i >= STATIC_LEN {
                        return (LineE::Bad, Ghost(0));
                    }
                    let (n, v) = static_entry(i as usize);
                    let fs = n.len() as u64 + v.len() as u64 + 32;
                    if fs > budget {
                        return (LineE::TooBig, Ghost(0));
                    }
                    out.push(n, v, false);
                    (LineE::Ok(e, fs), Ghost(fs as nat + 1))
                } else {
                    match dref_rel(t, ric, base, i) {
                        None => (LineE::Bad, Ghost(0)),
                        Some(a) => {
                            let en = t.abs(a);
                            let n = en.name.as_slice();
                            let v = en.value.as_slice();
                            proof {
                                lemma_tsize_entry(t.view().ents, (a - t.dropped) as int);
                            }
                            let fs = n.len() as u64 + v.len() as u64 + 32;
                            if fs > budget {
                                return (LineE::TooBig, Ghost(0));
                            }
                            out.push(n, v, false);
                            (LineE::Ok(e, fs), Ghost(fs as nat + 1))
                        },
                    }
                }
            },
            _ => (LineE::Bad, Ghost(0)),
        }
    } else if c >= 0x40 {
        match integer::decode(b, pos, 4) {
            IntE::Ok(i, e) => {
                let never = c % 64 >= 32;
                let stat = c % 32 >= 16;
                let (sr, g) = strings::read(b, e, 8, lim, s1, dt);
                let e2 = match sr {
                    StrE::Ok(e2) => e2,
                    _ => {
                        return (LineE::Bad, Ghost(0));
                    },
                };
                let n: &[u8] = if stat {
                    if i >= STATIC_LEN {
                        return (LineE::Bad, Ghost(0));
                    }
                    static_entry(i as usize).0
                } else {
                    match dref_rel(t, ric, base, i) {
                        None => {
                            return (LineE::Bad, Ghost(0));
                        },
                        Some(a) => {
                            proof {
                                lemma_tsize_entry(t.view().ents, (a - t.dropped) as int);
                            }
                            t.abs(a).name.as_slice()
                        },
                    }
                };
                proof {
                    assert(s1@.len() <= 8 * b@.len());
                }
                let fs = n.len() as u64 + s1.len() as u64 + 32;
                if fs > budget {
                    return (LineE::TooBig, Ghost(0));
                }
                out.push(n, s1.as_slice(), never);
                (LineE::Ok(e2, fs), Ghost(g@ + fs as nat + 1))
            },
            _ => (LineE::Bad, Ghost(0)),
        }
    } else if c >= 0x20 {
        let never = c % 32 >= 16;
        let (sr, g) = strings::read(b, pos, 4, lim, s1, dt);
        let e = match sr {
            StrE::Ok(e) => e,
            _ => {
                return (LineE::Bad, Ghost(0));
            },
        };
        let (sr2, g2) = strings::read(b, e, 8, lim, s2, dt);
        let e2 = match sr2 {
            StrE::Ok(e2) => e2,
            _ => {
                return (LineE::Bad, Ghost(0));
            },
        };
        proof {
            assert(s1@.len() <= 8 * b@.len());
            assert(s2@.len() <= 8 * b@.len());
        }
        let fs = s1.len() as u64 + s2.len() as u64 + 32;
        if fs > budget {
            return (LineE::TooBig, Ghost(0));
        }
        out.push(s1.as_slice(), s2.as_slice(), never);
        (LineE::Ok(e2, fs), Ghost(g@ + g2@ + fs as nat + 1))
    } else if c >= 0x10 {
        match integer::decode(b, pos, 4) {
            IntE::Ok(i, e) => {
                match dref_post(t, ric, base, i) {
                    None => (LineE::Bad, Ghost(0)),
                    Some(a) => {
                        let en = t.abs(a);
                        let n = en.name.as_slice();
                        let v = en.value.as_slice();
                        proof {
                            lemma_tsize_entry(t.view().ents, (a - t.dropped) as int);
                        }
                        let fs = n.len() as u64 + v.len() as u64 + 32;
                        if fs > budget {
                            return (LineE::TooBig, Ghost(0));
                        }
                        out.push(n, v, false);
                        (LineE::Ok(e, fs), Ghost(fs as nat + 1))
                    },
                }
            },
            _ => (LineE::Bad, Ghost(0)),
        }
    } else {
        match integer::decode(b, pos, 3) {
            IntE::Ok(i, e) => {
                let never = c % 16 >= 8;
                let (sr, g) = strings::read(b, e, 8, lim, s1, dt);
                let e2 = match sr {
                    StrE::Ok(e2) => e2,
                    _ => {
                        return (LineE::Bad, Ghost(0));
                    },
                };
                match dref_post(t, ric, base, i) {
                    None => (LineE::Bad, Ghost(0)),
                    Some(a) => {
                        let n = t.abs(a).name.as_slice();
                        proof {
                            lemma_tsize_entry(t.view().ents, (a - t.dropped) as int);
                            assert(s1@.len() <= 8 * b@.len());
                        }
                        let fs = n.len() as u64 + s1.len() as u64 + 32;
                        if fs > budget {
                            return (LineE::TooBig, Ghost(0));
                        }
                        out.push(n, s1.as_slice(), never);
                        (LineE::Ok(e2, fs), Ghost(g@ + fs as nat + 1))
                    },
                }
            },
            _ => (LineE::Bad, Ghost(0)),
        }
    }
}

/// The field lines of a section from `b[pos]` (`spec::lines`), into `out`
/// (cleared first). The second result is the work.
pub fn decode_lines(t: &DynTable, ric: u64, base: u64, max_size: u64, b: &[u8], e2: usize, out: &mut Fields, dt: &[u32]) -> (r: (Res, Ghost<nat>))
    requires
        t.inv(),
        ric <= icount(t.view()),
        old(out).inv(),
        e2 <= b@.len(),
        b@.len() <= 0x1000_0000,
        huffman::layout_ok(),
        huffman::dtab_ok(dt@),
    ensures
        final(out).inv(),
        match lines(t.view(), ric as nat, base as nat, max_size as nat, b@, e2 as int, 0, Seq::empty()) {
            SecR::Ok(f, k) => r.0 == Res::Done && final(out).view() == f && k == ric,
            SecR::Bad => r.0 == Res::Bad,
            SecR::TooBig => r.0 == Res::TooBig,
            SecR::Blocked(_) => false,
        },
        r.1@ <= 13 * b@.len() + max_size,
{
    let ghost tv = t.view();
    out.clear();
    let mut s1: Vec<u8> = Vec::new();
    let mut s2: Vec<u8> = Vec::new();
    let mut pos = e2;
    let mut size: u64 = 0;
    let ghost mut steps: nat = 0;
    let ghost res = lines(tv, ric as nat, base as nat, max_size as nat, b@, e2 as int, 0, Seq::empty());
    proof {
        lemma_lines_ric(tv, ric as nat, base as nat, max_size as nat, b@, e2 as int, 0, Seq::empty());
        assert(out.view() =~= Seq::<Field>::empty());
    }
    loop
        invariant
            t.inv(),
            tv == t.view(),
            ric <= icount(tv),
            out.inv(),
            e2 <= pos <= b@.len(),
            b@.len() <= 0x1000_0000,
            size <= max_size,
            huffman::layout_ok(),
            huffman::dtab_ok(dt@),
            res == lines(tv, ric as nat, base as nat, max_size as nat, b@, pos as int, size as nat, out.view()),
            res is Ok ==> res->Ok_1 == ric,
            !(res is Blocked),
            res == lines(tv, ric as nat, base as nat, max_size as nat, b@, e2 as int, 0, Seq::empty()),
            steps <= 13 * (pos - e2) + size,
        decreases b@.len() - pos,
    {
        if pos >= b.len() {
            return (Res::Done, Ghost(steps));
        }
        let (lr, g) = line_x(t, ric, base, b, pos, max_size - size, out, &mut s1, &mut s2, dt);
        match lr {
            LineE::Bad => {
                proof {
                    assert(line(tv, ric as nat, base as nat, b@, pos as int) is None);
                    assert(res is Bad);
                }
                return (Res::Bad, Ghost(0));
            },
            LineE::TooBig => {
                return (Res::TooBig, Ghost(0));
            },
            LineE::Ok(e, fs) => {
                proof {
                    steps = steps + g@;
                }
                pos = e;
                size = size + fs;
            },
        }
    }
}

pub proof fn lemma_without_len(bl: Seq<(nat, nat)>, s: nat)
    ensures
        without(bl, s).len() <= bl.len(),
    decreases bl.len(),
{
    if bl.len() > 0 {
        lemma_without_len(bl.drop_last(), s);
    }
}

/// `lines` gives back the Required Insert Count it was given.
proof fn lemma_lines_ric(t: Table, ric: nat, base: nat, ms: nat, b: Seq<u8>, pos: int, size: nat, acc: Seq<Field>)
    ensures
        lines(t, ric, base, ms, b, pos, size, acc) matches SecR::Ok(_, k) ==> k == ric,
        !(lines(t, ric, base, ms, b, pos, size, acc) is Blocked),
    decreases b.len() - pos,
{
    if 0 <= pos < b.len() {
        if let Some((f, e)) = line(t, ric, base, b, pos) {
            if !(e <= pos || e > b.len()) && !(size + fsize(f) > ms) {
                lemma_lines_ric(t, ric, base, ms, b, e, size + fsize(f), acc.push(f));
            }
        }
    }
}

impl Decoder {
    /// Whether `stream` is blocked.
    fn is_blocked(&self, stream: u64) -> (r: bool)
        ensures
            r == has_stream(bview(self.blocked@), stream as nat),
    {
        let mut i: usize = 0;
        while i < self.blocked.len()
            invariant
                i <= self.blocked@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.blocked@[j]).0 != stream,
            decreases self.blocked@.len() - i,
        {
            if self.blocked[i].0 == stream {
                proof {
                    assert(bview(self.blocked@)[i as int].0 == stream as nat);
                }
                return true;
            }
            i = i + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < bview(self.blocked@).len() implies #[trigger] bview(self.blocked@)[j].0 != stream as nat by {
                assert(self.blocked@[j].0 != stream);
            }
        }
        false
    }

    /// Decodes the field section `b` from stream `stream`
    /// (`spec::dec_section`), the field lines into `out`.
    pub fn decode(&mut self, stream: u64, b: &[u8], out: &mut Fields) -> (r: Res)
        requires
            old(self).inv(),
            old(out).inv(),
            b@.len() <= 0x1000_0000,
        ensures
            final(self).inv(),
            final(out).inv(),
            final(self).held@ == old(self).held@,
            ({
                let (d, st) = dec_section(old(self).state(), stream as nat, b@);
                &&& final(self).state() == st
                &&& match d {
                    Decoded::Done(f) => r == Res::Done && final(out).view() == f,
                    Decoded::Blocked => r == Res::Blocked,
                    Decoded::TooBig => r == Res::TooBig,
                    Decoded::Bad => r == Res::Bad,
                }
            }),
    {
        self.decode_metered(stream, b, out).0
    }

    /// `decode`, and its work: at most 13 steps per byte of the section,
    /// plus the size limit, plus twice the number of blocked streams.
    pub fn decode_metered(&mut self, stream: u64, b: &[u8], out: &mut Fields) -> (r: (Res, Ghost<nat>))
        requires
            old(self).inv(),
            old(out).inv(),
            b@.len() <= 0x1000_0000,
        ensures
            final(self).inv(),
            final(out).inv(),
            final(self).held@ == old(self).held@,
            ({
                let (d, st) = dec_section(old(self).state(), stream as nat, b@);
                &&& final(self).state() == st
                &&& match d {
                    Decoded::Done(f) => r.0 == Res::Done && final(out).view() == f,
                    Decoded::Blocked => r.0 == Res::Blocked,
                    Decoded::TooBig => r.0 == Res::TooBig,
                    Decoded::Bad => r.0 == Res::Bad,
                }
            }),
            r.1@ <= 13 * b@.len() + old(self).max_size + 2 * old(self).blocked@.len() + 2,
    {
        let ghost st0 = self.state();
        let ghost tv = self.table.view();
        let (enc, e1) = match integer::decode(b, 0, 8) {
            IntE::Ok(v, e) => (v, e),
            _ => {
                return (Res::Bad, Ghost(0));
            },
        };
        let total = self.table.icount();
        let ric = match decode_ric_x(enc, self.max_cap, total) {
            Some(r) => r,
            None => {
                return (Res::Bad, Ghost(0));
            },
        };
        let (delta, e2) = match integer::decode(b, e1, 7) {
            IntE::Ok(v, e) => (v, e),
            _ => {
                return (Res::Bad, Ghost(0));
            },
        };
        let sign = b[e1] >= 0x80;
        if sign && ric <= delta {
            return (Res::Bad, Ghost(0));
        }
        if ric > total {
            // Blocked (§2.1.2).
            if self.is_blocked(stream) {
                return (Res::Blocked, Ghost(self.blocked@.len() as nat));
            }
            if self.blocked.len() as u64 >= self.max_blocked {
                return (Res::Bad, Ghost(self.blocked@.len() as nat));
            }
            let ghost b0 = self.blocked@;
            self.blocked.push((stream, ric));
            proof {
                assert(bview(self.blocked@) =~= bview(b0).push((stream as nat, ric as nat)));
            }
            return (Res::Blocked, Ghost(self.blocked@.len() as nat));
        }
        let base = if sign { ric - delta - 1 } else { ric + delta };
        proof {
            assert(section(tv, st0.max_cap, st0.max_size, b@) == lines(tv, ric as nat, base as nat, st0.max_size, b@, e2 as int, 0, Seq::empty()));
        }
        let (lr, steps) = decode_lines(&self.table, ric, base, self.max_size, b, e2, out, self.dt);
        match lr {
            Res::Done => {},
            _ => {
                return (lr, Ghost(0));
            },
        }
        proof {
            lemma_without_len(bview(self.blocked@), stream as nat);
        }
        self.unblock(stream);
        if ric > 0 {
            proof {
                integer::lemma_pows();
                assert(integer::P2@[7] as nat == p2(7));
            }
            integer::encode(&mut self.out, 0x80, 7, stream);
            if ric > self.acked {
                self.acked = ric;
            }
        }
        (Res::Done, Ghost(steps@ + self.blocked@.len() as nat + 1))
    }
}

} // verus!
