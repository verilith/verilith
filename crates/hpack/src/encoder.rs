//! The verified HPACK encoder (RFC 7541), proven against the decoder's
//! specification.
//!
//! The encoder keeps a copy of the peer decoder's state (`Encoder::state`,
//! a `spec::DState`): the dynamic table, its maximum size, the peer's
//! SETTINGS_HEADER_TABLE_SIZE and the size update it is owed. The theorem
//! (`Encoder::encode`) is that the bytes of a header block decode, by
//! `spec::block`, from that state to exactly the fields given, and leave
//! the decoder in the encoder's next state:
//!
//! ```text
//! block(state, encode(fields)) == Some((fields, s2)),  end_block(s2) == state'
//! ```
//!
//! so the peer's decoder and the encoder never disagree about the dynamic
//! table. Which representation the encoder picks for a field (indexed,
//! literal with or without indexing, Huffman or not) is a policy and is
//! not part of the theorem: every choice is proven.
use crate::emit::*;
use crate::hencode;
#[cfg(verus_keep_ghost)]
use crate::hencode::enc_ok;
use crate::sindex::*;
use crate::spec::*;
use crate::table::*;
use vstd::prelude::*;

verus! {

/// A header field to encode.
pub struct Header<'a> {
    /// The name. HTTP/2 needs it lowercase (RFC 9113 §8.2.1); HPACK itself
    /// does not care.
    pub name: &'a [u8],
    /// The value.
    pub value: &'a [u8],
    /// Encode as "never indexed" (§6.2.3): the field is not added to the
    /// dynamic table, is not matched against it, and intermediaries must
    /// not index it either. For credentials, cookies and other values an
    /// attacker could probe by compression (§7.1.3).
    pub sensitive: bool,
}

/// What the peer decodes a `Header` as.
pub open spec fn hfield<'a>(h: Header<'a>) -> Field {
    Field { name: h.name@, value: h.value@, never: h.sensitive }
}

pub open spec fn hfields<'a>(hs: Seq<Header<'a>>) -> Seq<Field> {
    hs.map_values(|h: Header<'a>| hfield(h))
}

/// `w` is a header block that decodes from `st` to the fields `fs`,
/// leaving the decoder, after the block ends, in `st2`.
pub open spec fn encodes(st: DState, w: Seq<u8>, fs: Seq<Field>, st2: DState) -> bool {
    match block(st, w) {
        Some((gs, s3)) => gs == fs && end_block(s3) == st2,
        None => false,
    }
}

/// Every name and value is at most `MAX_STR` bytes, the longest string the
/// decoder accepts.
pub open spec fn fits<'a>(hs: Seq<Header<'a>>) -> bool {
    forall|i: int| 0 <= i < hs.len() ==> #[trigger] hs[i].name@.len() <= MAX_STR && hs[i].value@.len() <= MAX_STR
}

/// `a == b`. Trusted: slice equality is what it says (a `memcmp`).
#[verifier::external_body]
#[inline(always)]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    a == b
}

/// Checks `fits`.
fn check_fits(hs: &[Header]) -> (r: bool)
    ensures
        r == fits(hs@),
{
    let mut i: usize = 0;
    while i < hs.len()
        invariant
            i <= hs@.len(),
            fits(hs@.subrange(0, i as int)),
        decreases hs@.len() - i,
    {
        if hs[i].name.len() > 65536 || hs[i].value.len() > 65536 {
            proof {
                assert(!(hs@[i as int].name@.len() <= MAX_STR && hs@[i as int].value@.len() <= MAX_STR));
            }
            return false;
        }
        proof {
            assert forall|k: int| 0 <= k < i + 1 implies #[trigger] hs@.subrange(0, i + 1)[k].name@.len() <= MAX_STR
                && hs@.subrange(0, i + 1)[k].value@.len() <= MAX_STR by {
                if k < i {
                    assert(hs@.subrange(0, i as int)[k] == hs@.subrange(0, i + 1)[k]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(hs@.subrange(0, i as int) =~= hs@);
    }
    true
}

/// An HPACK encoder: the peer decoder's state, and the table size the
/// encoder would like.
pub struct Encoder {
    /// The dynamic table (the encoder's copy of the peer's).
    pub table: Table,
    /// The peer's SETTINGS_HEADER_TABLE_SIZE, as its decoder applies it.
    pub settings: u32,
    /// The lowest limit announced since the last size update, or
    /// `NO_LIMIT` (`DState::pending`).
    pub pending: u32,
    /// The next block must start with a size update (`DState::expect`).
    pub expect: bool,
    /// The table size the encoder uses when the peer allows it.
    pub target: u32,
    /// An index of the dynamic table, for lookups: an entry is recorded in
    /// one of two slots chosen by a hash of its name and value, and in one
    /// of two chosen by a hash of its name (in each pair, the one holding
    /// the older entry), as the low 16 bits of `table.ins` just after it
    /// was added. Only a hint: a candidate it gives is compared with the
    /// entry.
    pub ix: Vec<u16>,
}

/// The index's size.
pub const IX: usize = 512;

const K: u64 = 0x9E37_79B9_7F4A_7C15;

/// A hash of `s`, for the encoder's index. Not trusted: a candidate the
/// index gives is always compared with the table entry.
#[inline(always)]
fn hash(s: &[u8], seed: u64) -> u64 {
    let n = s.len();
    let mut h = seed ^ (n as u64);
    if n >= 8 {
        let mut i: usize = 0;
        while n - i > 8
            invariant
                n == s@.len(),
                n >= 8,
                i <= n,
            decreases n - i,
        {
            h = (h.rotate_left(5) ^ verilith_core::prims::load_u64_le(s, i)).wrapping_mul(K);
            i = i + 8;
        }
        (h.rotate_left(5) ^ verilith_core::prims::load_u64_le(s, n - 8)).wrapping_mul(K)
    } else {
        let mut t: u64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == s@.len(),
                i <= n,
            decreases n - i,
        {
            t = (t << 8) | s[i] as u64;
            i = i + 1;
        }
        (h.rotate_left(5) ^ t).wrapping_mul(K)
    }
}

/// The two index slots of a name and value, and the two of a name.
#[inline(always)]
fn slots(hn: u64, hf: u64) -> (r: (usize, usize, usize, usize))
    ensures
        r.0 < IX,
        r.1 < IX,
        r.2 < IX,
        r.3 < IX,
{
    (
        ((hf >> 40) % 256) as usize,
        ((hf >> 52) % 256) as usize,
        256 + ((hn >> 40) % 256) as usize,
        256 + ((hn >> 52) % 256) as usize,
    )
}
impl Encoder {
    /// The peer decoder's state between header blocks.
    pub open spec fn state(&self) -> DState {
        DState {
            table: self.table.view(),
            max: self.table.max as nat,
            settings: self.settings as nat,
            pending: self.pending as nat,
            at_start: true,
            expect: self.expect,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.table.inv()
        &&& enc_ok()
        &&& self.ix@.len() == IX
    }

    /// An encoder for a peer in the initial state (a 4096-byte table), or
    /// `None` if the Huffman table check fails (it does not: see
    /// tests/tables.rs).
    pub fn new() -> (r: Option<Encoder>)
        ensures
            r matches Some(e) ==> e.inv() && e.state() == initial() && e.target == 4096,
    {
        if !hencode::ready() {
            return None;
        }
        let e = Encoder {
            table: Table::with_capacity(4096, 32),
            settings: 4096,
            pending: NO_LIMIT,
            expect: false,
            target: 4096,
            ix: vec![0u16; IX],
        };
        proof {
            assert(e.state().table =~= initial().table);
        }
        Some(e)
    }

    /// The peer's SETTINGS_HEADER_TABLE_SIZE changed to `n`. Call it at the
    /// point in the output where the peer's decoder applies the new value:
    /// after the last header block sent before the SETTINGS ACK. As
    /// nghttp2's decoder does, a lower limit shrinks the table at once, and
    /// the next block starts with a size update.
    pub fn change_settings(&mut self, n: u32)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).state() == crate::spec::change_settings(old(self).state(), n as nat),
            final(self).target == old(self).target,
    {
        if self.table.max > n {
            self.settings = n;
            let _ = self.table.resize(n);
            self.pending = n;
            self.expect = true;
        } else {
            self.settings = n;
        }
    }

    /// Sets the table size the encoder uses, within the peer's limit. It
    /// takes effect, with a size update, at the start of the next block.
    pub fn set_table_size(&mut self, n: u32)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).state() == old(self).state(),
            final(self).target == n,
    {
        self.target = n;
    }

    /// The fields of the static and dynamic tables matching `name` and
    /// `value`: an index of an entry equal to both, and of one with that
    /// name; 0 for none; and the hashes of the name and of the name and
    /// value when the dynamic table was searched. The static table is
    /// searched through a perfect hash of its names (`sindex.rs`), the
    /// dynamic table through `ix`; neither is trusted, every candidate is
    /// compared with the entry.
    fn find(&self, name: &[u8], value: &[u8]) -> (r: (usize, usize, u64, u64))
        requires
            self.table.inv(),
            self.ix@.len() == IX,
        ensures
            r.0 != 0 ==> 1 <= r.0 <= self.table.view().len() + 61 && entry(self.table.view(), r.0 as nat) == (
                name@,
                value@,
            ),
            r.1 != 0 ==> 1 <= r.1 <= self.table.view().len() + 61 && entry(self.table.view(), r.1 as nat).0 == name@,
            r.0 <= 0x0800_0000 + 61,
            r.1 <= 0x0800_0000 + 61,
    {
        let mut nidx: usize = 0;
        let n = name.len();
        if n >= 2 {
            let hs = (n % 256 + SH_A * (name[1] as usize) + SH_C * (name[n - 1] as usize)) % 256;
            let f = NAME_AT[hs] as usize;
            if 1 <= f && f <= 61 {
                let (sn, _) = static_entry(f - 1);
                if bytes_eq(sn, name) {
                    nidx = f;
                    let end = f + NAME_CNT[f] as usize;
                    let mut j = f;
                    while j < end && j <= 61
                        invariant
                            1 <= f <= j,
                            nidx == f,
                            entry(self.table.view(), f as nat).0 == name@,
                        decreases end - j,
                    {
                        let (sn2, sv2) = static_entry(j - 1);
                        if bytes_eq(sv2, value) && bytes_eq(sn2, name) {
                            return (j, nidx, 0, 0);
                        }
                        j = j + 1;
                    }
                }
            }
        }
        // A name in the static table is hashed as its index there.
        let hn = if nidx != 0 {
            (nidx as u64).wrapping_mul(K)
        } else {
            hash(name, 0)
        };
        let hf = hash(value, hn);
        let (f1, f2, n1, n2) = slots(hn, hf);
        let i1 = self.probe(f1, name, value, true);
        if i1 != 0 {
            return (i1, if nidx != 0 { nidx } else { i1 }, hn, hf);
        }
        let i2 = self.probe(f2, name, value, true);
        if i2 != 0 {
            return (i2, if nidx != 0 { nidx } else { i2 }, hn, hf);
        }
        if nidx == 0 {
            nidx = self.probe(n1, name, value, false);
            if nidx == 0 {
                nidx = self.probe(n2, name, value, false);
            }
        }
        (0, nidx, hn, hf)
    }

    /// The dynamic table entry `ix[slot]` names, if it has this name (and
    /// value, with `both`): its index, or 0.
    #[inline(always)]
    fn probe(&self, slot: usize, name: &[u8], value: &[u8], both: bool) -> (r: usize)
        requires
            self.table.inv(),
            slot < self.ix@.len(),
        ensures
            r != 0 ==> 62 <= r <= self.table.view().len() + 61 && entry(self.table.view(), r as nat).0 == name@,
            r != 0 && both ==> entry(self.table.view(), r as nat).1 == value@,
            r <= 0x0800_0000 + 61,
    {
        let j = (self.table.ins as u16).wrapping_sub(self.ix[slot]) as usize;
        if j < self.table.len() {
            let (en, ev) = self.table.get(62 + j);
            if (!both || bytes_eq(ev, value)) && bytes_eq(en, name) {
                return 62 + j;
            }
        }
        0
    }

    /// The age of the entry `ix[slot]` names (0 for the newest; at least
    /// the table's length for none).
    #[inline(always)]
    fn age(&self, slot: usize) -> usize
        requires
            slot < self.ix@.len(),
    {
        (self.table.ins as u16).wrapping_sub(self.ix[slot]) as usize
    }

    /// Whether to add a field to the dynamic table (a policy, not part of
    /// the theorem). Like nghttp2: not the fields whose values seldom
    /// repeat or that hold secrets (found by their static name index), and
    /// not one that would take more than three quarters of the table.
    #[inline(always)]
    fn should_index(&self, nidx: usize, nlen: usize, vlen: usize) -> bool
        requires
            nlen <= MAX_STR,
            vlen <= MAX_STR,
    {
        // :path, age, authorization, content-length, etag,
        // if-modified-since, if-none-match, location, set-cookie; and a
        // cookie shorter than 20 bytes (nghttp2 and Firefox never index
        // those two; here they are sent without indexing, and a caller
        // that wants "never indexed" sets `sensitive`).
        if nidx == 4 || nidx == 5 || nidx == 21 || nidx == 23 || nidx == 28 || nidx == 34 || nidx == 40 || nidx
            == 41 || nidx == 46 || nidx == 55 || (nidx == 32 && vlen < 20) {
            return false;
        }
        let sz = nlen as u64 + vlen as u64 + 32;
        sz * 4 <= (self.table.max as u64) * 3
    }

    /// Encodes one field, from the decoder state `cur` inside a block.
    #[verifier::rlimit(40)]
    fn field(&mut self, h: &Header, out: &mut Vec<u8>, Ghost(cur): Ghost<DState>) -> (r: Ghost<DState>)
        requires
            old(self).inv(),
            h.name@.len() <= MAX_STR,
            h.value@.len() <= MAX_STR,
            cur.table == old(self).table.view(),
            cur.max == old(self).table.max as nat,
            !cur.expect,
        ensures
            final(self).inv(),
            final(self).table.max == old(self).table.max,
            final(self).settings == old(self).settings,
            final(self).pending == old(self).pending,
            final(self).expect == old(self).expect,
            final(self).target == old(self).target,
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
            block(cur, final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int)) == Some(
                (seq![hfield(*h)], r@),
            ),
            r@ == after_field(cur, final(self).table.view()),
    {
        hide(rep);
        hide(block);
        hide(enc_ok);
        let ghost o0 = out@;
        let (full, nidx, hname, hfull) = self.find(h.name, h.value);
        if !h.sensitive && full != 0 {
            put_int(out, 0x80, 7, full as u32);
            proof {
                lemma_rep_idx(cur, full as nat);
                let w = int_enc(0x80, 7, full as nat);
                assert(out@.subrange(o0.len() as int, out@.len() as int) =~= w);
                assert(out@.subrange(0, o0.len() as int) =~= o0);
                lemma_block_field(cur, w, hfield(*h), after_field(cur, cur.table));
            }
            return Ghost(after_field(cur, cur.table));
        }
        let kind = if h.sensitive {
            NEVER
        } else if self.should_index(nidx, h.name.len(), h.value.len()) {
            INCR
        } else {
            NOIDX
        };
        let (fl, nb): (u8, u8) = if kind == INCR {
            (0x40, 6)
        } else if kind == NOIDX {
            (0, 4)
        } else {
            (0x10, 4)
        };
        put_int(out, fl, nb, nidx as u32);
        let ghost mut hn = false;
        let ghost mut rawn = Seq::<u8>::empty();
        if nidx == 0 {
            let g = put_str(out, h.name);
            proof {
                hn = g@.0;
                rawn = g@.1;
            }
        }
        let gv = put_str(out, h.value);
        if kind == INCR {
            self.table.insert_copy(h.name, h.value);
            let (f1, f2, n1, n2) = slots(hname, hfull);
            let sf = if self.age(f1) >= self.age(f2) { f1 } else { f2 };
            let sn = if self.age(n1) >= self.age(n2) { n1 } else { n2 };
            let now = self.table.ins as u16;
            self.ix.set(sf, now);
            self.ix.set(sn, now);
        }
        proof {
            let (hv, rawv) = gv@;
            lemma_rep_lit(cur, kind, nidx as nat, hn, rawn, h.name@, hv, rawv, h.value@);
            let w = lit_enc(kind, nidx as nat, hn, rawn, hv, rawv);
            assert(out@.subrange(o0.len() as int, out@.len() as int) =~= w);
            assert(out@.subrange(0, o0.len() as int) =~= o0);
            lemma_block_field(cur, w, hfield(*h), after_field(cur, self.table.view()));
        }
        Ghost(after_field(cur, self.table.view()))
    }

    /// Starts a header block: the size updates the peer is owed or the
    /// encoder wants, if any. At most two: the lowest limit announced
    /// since the last update, when it is below the size the encoder will
    /// use (§4.2), then that size.
    #[verifier::rlimit(40)]
    fn start(&mut self, out: &mut Vec<u8>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).target == old(self).target,
            !final(self).expect,
            final(out)@.len() >= old(out)@.len(),
            final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
            block(old(self).state(), final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int)) == Some(
                (Seq::<Field>::empty(), final(self).state()),
            ),
    {
        hide(rep);
        hide(block);
        hide(enc_ok);
        hide(evict);
        let ghost o0 = out@;
        let ghost st0 = self.state();
        let d = if self.target < self.settings {
            self.target
        } else {
            self.settings
        };
        if !self.expect && self.table.max == d {
            proof {
                assert(out@.subrange(o0.len() as int, out@.len() as int) =~= Seq::<u8>::empty());
                assert(out@.subrange(0, o0.len() as int) =~= o0);
                lemma_block_empty(st0);
            }
            return;
        }
        let ghost mut w1 = Seq::<u8>::empty();
        if self.pending < d {
            let p = self.pending;
            put_int(out, 0x20, 5, p);
            proof {
                lemma_rep_upd(st0, p as nat);
                w1 = int_enc(0x20, 5, p as nat);
            }
            let _ = self.table.resize(p);
            self.pending = NO_LIMIT;
            self.expect = false;
            proof {
                lemma_block_update(st0, w1, self.state());
            }
        }
        let ghost st1 = self.state();
        proof {
            if w1.len() == 0 {
                assert(st1 == st0);
            }
        }
        put_int(out, 0x20, 5, d);
        proof {
            lemma_rep_upd(st1, d as nat);
        }
        let _ = self.table.resize(d);
        self.pending = NO_LIMIT;
        self.expect = false;
        proof {
            let w2 = int_enc(0x20, 5, d as nat);
            lemma_block_update(st1, w2, self.state());
            assert(out@.subrange(o0.len() as int, out@.len() as int) =~= w1 + w2);
            assert(out@.subrange(0, o0.len() as int) =~= o0);
            if w1.len() == 0 {
                assert(w1 + w2 =~= w2);
            } else {
                lemma_block_append(st0, w1, w2);
                assert(Seq::<Field>::empty() + Seq::<Field>::empty() =~= Seq::<Field>::empty());
            }
        }
    }

    /// Encodes a header block: appends to `out` the representations of the
    /// fields `hs`, in order, starting with any size update owed. They
    /// decode, from the peer's state before, to exactly `hs` (with
    /// `never` set for the sensitive ones), and leave the peer in the
    /// encoder's state after. False, with nothing written or changed, if a
    /// name or value is longer than 65536 bytes (the decoder's limit).
    #[verifier::rlimit(40)]
    pub fn encode(&mut self, hs: &[Header], out: &mut Vec<u8>) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).target == old(self).target,
            ok == fits(hs@),
            !ok ==> final(out)@ == old(out)@ && final(self).state() == old(self).state(),
            ok ==> final(out)@.len() >= old(out)@.len(),
            ok ==> final(out)@.subrange(0, old(out)@.len() as int) == old(out)@,
            ok ==> encodes(
                old(self).state(),
                final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int),
                hfields(hs@),
                final(self).state(),
            ),
    {
        hide(rep);
        hide(block);
        hide(enc_ok);
        hide(evict);
        hide(insert);
        if !check_fits(hs) {
            return false;
        }
        let mut i: usize;
        let ghost st0 = self.state();
        let ghost o0 = out@;
        self.start(out);
        let ghost mut cur = self.state();
        proof {
            assert(hfields(hs@.subrange(0, 0)) =~= Seq::<Field>::empty());
        }
        i = 0;
        while i < hs.len()
            invariant
                i <= hs@.len(),
                fits(hs@),
                self.inv(),
                self.target == old(self).target,
                !self.expect,
                out@.len() >= o0.len(),
                out@.subrange(0, o0.len() as int) == o0,
                o0 == old(out)@,
                st0 == old(self).state(),
                block(st0, out@.subrange(o0.len() as int, out@.len() as int)) == Some(
                    (hfields(hs@.subrange(0, i as int)), cur),
                ),
                cur == (DState { at_start: i == 0, ..self.state() }),
            decreases hs@.len() - i,
        {
            let ghost w = out@.subrange(o0.len() as int, out@.len() as int);
            let ghost ol = out@;
            proof {
                assert(hs@[i as int].name@.len() <= MAX_STR && hs@[i as int].value@.len() <= MAX_STR);
            }
            let nx = self.field(&hs[i], out, Ghost(cur));
            proof {
                let piece = out@.subrange(ol.len() as int, out@.len() as int);
                assert(out@.subrange(o0.len() as int, out@.len() as int) =~= w + piece);
                assert(out@.subrange(0, o0.len() as int) =~= o0) by {
                    assert(out@.subrange(0, o0.len() as int) =~= out@.subrange(0, ol.len() as int).subrange(
                        0,
                        o0.len() as int,
                    ));
                }
                lemma_block_append(st0, w, piece);
                assert(hfields(hs@.subrange(0, i + 1)) =~= hfields(hs@.subrange(0, i as int)) + seq![
                    hfield(hs@[i as int]),
                ]);
                cur = nx@;
            }
            i = i + 1;
        }
        proof {
            assert(hs@.subrange(0, i as int) =~= hs@);
            assert(end_block(cur) == self.state());
        }
        true
    }
}

} // verus!
