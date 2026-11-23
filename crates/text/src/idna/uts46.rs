//! UTS #46 processing, verified against `spec`.
use super::super::unicode::data::*;
use super::super::unicode::norm::{decode as decode_utf8, decode_all, encode_all, normalize_into, quick_check};
#[cfg(verus_only)]
use super::super::unicode::norm::{lemma_ascii_all, lemma_ascii_stable, lemma_enc_char, lemma_enc_len_full, lemma_enc_whole, lemma_nf_scalars};
use super::super::unicode::spec::*;
use super::super::unicode::tables::FLAG_FAST_NFC;
use super::data::*;
use super::punycode::{decode_into, encode_append};
#[cfg(verus_only)]
use super::punycode::lemma_decode_scalars;
#[cfg(verus_only)]
use super::punycode::{decode, encode};
use super::spec::*;
use super::tables::*;
#[cfg(verus_only)]
use verilith_core::utf8::utf8_encode;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Mapping and normalization
// ---------------------------------------------------------------------------

proof fn lemma_map_one_scalars(c: u32, t: bool)
    requires
        is_scalar(c),
    ensures
        scalars(map_one(c, t)),
{
    axiom_idna_mapping(c);
    assert forall|k: int| 0 <= k < map_one(c, t).len() implies is_scalar(#[trigger] map_one(c, t)[k]) by {
        if t && c == 0x1E9E {
        } else if map_one(c, t) != seq![c] {
            assert(map_one(c, t)[k] == idna_pool(map_off(c) + k));
        }
    }
}

proof fn lemma_scalars_append(a: Seq<u32>, b: Seq<u32>)
    requires
        scalars(a),
        scalars(b),
    ensures
        scalars(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies is_scalar(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// Step 1, Map, on the UTF-8 encoding `s` of `cs`, decoding as it goes.
fn map_utf8(s: &[u8], t: bool, Ghost(cs): Ghost<Seq<u32>>, buf: Vec<u32>) -> (r: Vec<u32>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r@ == map_all(cs, t),
        scalars(r@),
{
    let n = s.len();
    // `buf` is only storage: its contents are dropped and its capacity reused.
    let mut r: Vec<u32> = buf;
    r.clear();
    r.reserve(n);
    let mut i = 0;
    let ghost mut k: int = 0;
    proof {
        assert(cs.take(0) =~= Seq::<u32>::empty());
        lemma_enc_whole(cs, 0);
    }
    while i < n
        invariant
            n == s@.len(),
            s@ == enc(cs),
            scalars(cs),
            0 <= k <= cs.len(),
            i == enc(cs.take(k)).len(),
            i <= n,
            r@ == map_all(cs.take(k), t),
            scalars(r@),
        decreases n - i,
    {
        proof {
            if k == cs.len() {
                assert(cs.take(k) =~= cs);
            }
            lemma_enc_char(s@, cs, k);
        }
        let (c, len) = decode_utf8(s, i, Ghost(cs[k]));
        let w = iword_of(c);
        let st = w & 7;
        let ghost r0 = r@;
        if t && c == 0x1E9E {
            r.push(0x73);
            r.push(0x73);
            proof {
                assert(r@ =~= r0 + map_one(c, t));
            }
        } else if st == STATUS_IGNORED {
            proof {
                assert(r@ =~= r0 + map_one(c, t));
            }
        } else if st == STATUS_MAPPED || (st == STATUS_DEVIATION && t) {
            push_mapping(&mut r, c, w);
        } else {
            r.push(c);
            proof {
                assert(r@ =~= r0 + map_one(c, t));
            }
        }
        proof {
            assert(cs.take(k + 1).drop_last() =~= cs.take(k));
            assert(is_scalar(cs[k]));
            lemma_map_one_scalars(c, t);
            lemma_scalars_append(r0, map_one(c, t));
        }
        i += len;
        proof {
            k = k + 1;
        }
    }
    proof {
        lemma_enc_len_full(cs, k);
        assert(cs.take(cs.len() as int) =~= cs);
    }
    r
}

/// Step 2, Normalize.
fn nfc_exec(m: Vec<u32>) -> (r: Vec<u32>)
    requires
        scalars(m@),
    ensures
        r@ == nf(m@, true, false),
        scalars(r@),
{
    if nfc_fast(m.as_slice()) {
        return m;
    }
    let mut mb: Vec<u8> = Vec::with_capacity(if m.len() < 0x1000_0000 { m.len() * 4 } else { m.len() });
    encode_all(m.as_slice(), &mut mb);
    proof {
        assert(mb@ =~= enc(m@));
    }
    if quick_check(mb.as_slice(), true, false, Ghost(m@)) {
        return m;
    }
    let mut nb: Vec<u8> = Vec::with_capacity(mb.len());
    normalize_into(mb.as_slice(), true, false, &mut nb, Ghost(m@));
    proof {
        assert(nb@ =~= enc(nf(m@, true, false)));
        lemma_nf_scalars(m@, true, false);
    }
    decode_all(nb.as_slice(), Ghost(nf(m@, true, false)))
}

/// Whether every character of `l` is NFC-fast, so that `l` is in NFC.
fn nfc_fast(l: &[u32]) -> (r: bool)
    requires
        scalars(l@),
    ensures
        r ==> nf(l@, true, false) == l@,
{
    let mut k = 0;
    while k < l.len()
        invariant
            k <= l@.len(),
            scalars(l@),
            forall|q: int| 0 <= q < k ==> stable(#[trigger] l@[q], true, false),
        decreases l@.len() - k,
    {
        let c = l[k];
        let f = flags_of(c);
        if f & FLAG_FAST_NFC == 0 {
            return false;
        }
        proof {
            assert(is_scalar(l@[k as int]));
            assert(fast_flag(true, false) == FLAG_FAST_NFC);
            assert(f & FLAG_FAST_NFC != 0);
            assert(has_flag(c, FLAG_FAST_NFC));
            axiom_fast(c, true, false);
        }
        k += 1;
    }
    proof {
        lemma_nf_stable_run(seq![], l@, true, false);
        assert(Seq::<u32>::empty() + l@ =~= l@);
        lemma_nf_empty();
    }
    true
}

/// Whether `l` is in NFC (criterion 1).
fn is_nfc_exec(l: &[u32]) -> (r: bool)
    requires
        scalars(l@),
    ensures
        r == (nf(l@, true, false) == l@),
{
    if nfc_fast(l) {
        return true;
    }
    let n = nfc_exec(vstd::slice::slice_to_vec(l));
    if n.len() != l.len() {
        return false;
    }
    let mut k = 0;
    while k < l.len()
        invariant
            n@.len() == l@.len(),
            n@ == nf(l@, true, false),
            k <= l@.len(),
            forall|q: int| 0 <= q < k ==> n@[q] == l@[q],
        decreases l@.len() - k,
    {
        if n[k] != l[k] {
            assert(n@[k as int] != l@[k as int]);
            return false;
        }
        k += 1;
    }
    proof {
        assert(n@ =~= l@);
    }
    true
}

// ---------------------------------------------------------------------------
// Validity
// ---------------------------------------------------------------------------

#[inline(always)]
fn status_ok_exec(c: u32, w: u32, t: bool, std3: bool) -> (r: bool)
    requires
        w == iword(c),
    ensures
        r == status_ok(c, t, std3),
{
    let st = w & 7;
    (st == STATUS_VALID || (!t && st == STATUS_DEVIATION)) && (!(std3 && c < 0x80) || ((0x61 <= c && c <= 0x7A) || (
    0x30 <= c && c <= 0x39) || c == HYPHEN))
}

fn joins_left_exec(l: &[u32], j: usize) -> (r: bool)
    requires
        j <= l@.len(),
    ensures
        r == joins_left(l@, j - 1),
{
    let mut q = j;
    while q > 0
        invariant
            q <= j <= l@.len(),
            joins_left(l@, j - 1) == joins_left(l@, q - 1),
        decreases q,
    {
        let jt = (iword_of(l[q - 1]) >> 8) & 7;
        if jt == JT_L || jt == JT_D {
            return true;
        }
        if jt != JT_T {
            return false;
        }
        q -= 1;
    }
    false
}

fn joins_right_exec(l: &[u32], j: usize) -> (r: bool)
    requires
        j <= l@.len(),
    ensures
        r == joins_right(l@, j as int),
{
    let mut q = j;
    while q < l.len()
        invariant
            j <= q <= l@.len(),
            joins_right(l@, j as int) == joins_right(l@, q as int),
        decreases l@.len() - q,
    {
        let jt = (iword_of(l[q]) >> 8) & 7;
        if jt == JT_R || jt == JT_D {
            return true;
        }
        if jt != JT_T {
            return false;
        }
        q += 1;
    }
    false
}

fn joiner_ok_exec(l: &[u32], k: usize) -> (r: bool)
    requires
        k < l@.len(),
    ensures
        r == joiner_ok(l@, k as int),
{
    let _n = l.len();
    let c = l[k];
    if c != ZWNJ && c != ZWJ {
        return true;
    }
    if k == 0 {
        return false;
    }
    if ccc_of(l[k - 1]) == VIRAMA {
        return true;
    }
    c == ZWNJ && joins_left_exec(l, k) && joins_right_exec(l, k + 1)
}

/// The validity criteria but CheckBidi.
fn valid_exec(l: &[u32], o: Options, t: bool) -> (r: bool)
    requires
        scalars(l@),
    ensures
        r == valid(l@, o, t),
{
    let n = l.len();
    if o.check_hyphens {
        if n >= 4 && l[2] == HYPHEN && l[3] == HYPHEN {
            return false;
        }
        if n > 0 && (l[0] == HYPHEN || l[n - 1] == HYPHEN) {
            return false;
        }
    } else if n >= 4 && l[0] == 0x78 && l[1] == 0x6E && l[2] == HYPHEN && l[3] == HYPHEN {
        return false;
    }
    if n > 0 && iword_of(l[0]) & 8 != 0 {
        return false;
    }
    let mut k = 0;
    while k < n
        invariant
            n == l@.len(),
            k <= n,
            forall|q: int| 0 <= q < k ==> l@[q] != DOT,
            forall|q: int| 0 <= q < k ==> status_ok(#[trigger] l@[q], t, o.use_std3_ascii_rules),
            o.check_joiners ==> forall|q: int| 0 <= q < k ==> #[trigger] joiner_ok(l@, q),
        decreases n - k,
    {
        let c = l[k];
        if c == DOT {
            assert(l@.contains(DOT));
            return false;
        }
        if !status_ok_exec(c, iword_of(c), t, o.use_std3_ascii_rules) {
            return false;
        }
        if o.check_joiners && !joiner_ok_exec(l, k) {
            return false;
        }
        k += 1;
    }
    is_nfc_exec(l)
}

// ---------------------------------------------------------------------------
// CheckBidi
// ---------------------------------------------------------------------------

#[inline(always)]
fn bidi_of(c: u32) -> (r: u32)
    ensures
        r == bidi(c),
{
    (iword_of(c) >> 4) & 15
}

fn has_rtl_exec(l: &[u32]) -> (r: bool)
    ensures
        r == exists|k: int| 0 <= k < l@.len() && rtl(bidi(#[trigger] l@[k])),
{
    let mut k = 0;
    while k < l.len()
        invariant
            k <= l@.len(),
            forall|q: int| 0 <= q < k ==> !rtl(bidi(#[trigger] l@[q])),
        decreases l@.len() - k,
    {
        let b = bidi_of(l[k]);
        if b == BIDI_R || b == BIDI_AL || b == BIDI_AN {
            assert(rtl(bidi(l@[k as int])));
            return true;
        }
        k += 1;
    }
    false
}

fn bidi_ok_exec(l: &[u32]) -> (r: bool)
    requires
        l@.len() > 0,
    ensures
        r == bidi_ok(l@),
{
    let n = l.len();
    let f = bidi_of(l[0]);
    let is_l = f == BIDI_L;
    if !is_l && f != BIDI_R && f != BIDI_AL {
        return false;
    }
    // The last character that is not a nonspacing mark.
    let mut e = n;
    while e > 0 && bidi_of(l[e - 1]) == BIDI_NSM
        invariant
            1 <= e <= n == l@.len(),
            bidi(l@[0]) != BIDI_NSM,
            last_non_nsm(l@, n - 1) == last_non_nsm(l@, e - 1),
        decreases e,
    {
        e -= 1;
    }
    proof {
        if e == 0 {
            assert(last_non_nsm(l@, -1) == -1);
        }
    }
    // `l[0]` is not a nonspacing mark.
    assert(e > 0);
    let eb = bidi_of(l[e - 1]);
    if is_l {
        if !(eb == BIDI_L || eb == BIDI_EN) {
            return false;
        }
    } else if !(eb == BIDI_R || eb == BIDI_AL || eb == BIDI_EN || eb == BIDI_AN) {
        return false;
    }
    let mut en = false;
    let mut an = false;
    let mut k = 0;
    while k < n
        invariant
            n == l@.len(),
            k <= n,
            is_l == (bidi(l@[0]) == BIDI_L),
            is_l ==> forall|q: int| 0 <= q < k ==> ltr_allowed(bidi(#[trigger] l@[q])),
            !is_l ==> forall|q: int| 0 <= q < k ==> rtl_allowed(bidi(#[trigger] l@[q])),
            en == exists|q: int| 0 <= q < k && bidi(#[trigger] l@[q]) == BIDI_EN,
            an == exists|q: int| 0 <= q < k && bidi(#[trigger] l@[q]) == BIDI_AN,
        decreases n - k,
    {
        let b = bidi_of(l[k]);
        if is_l {
            if !(b == BIDI_L || b == BIDI_EN || b == BIDI_ES || b == BIDI_CS || b == BIDI_ET || b == BIDI_ON || b
                == BIDI_BN || b == BIDI_NSM) {
                return false;
            }
        } else if !(b == BIDI_R || b == BIDI_AL || b == BIDI_AN || b == BIDI_EN || b == BIDI_ES || b == BIDI_CS || b
            == BIDI_ET || b == BIDI_ON || b == BIDI_BN || b == BIDI_NSM) {
            return false;
        }
        if b == BIDI_EN {
            en = true;
        }
        if b == BIDI_AN {
            an = true;
        }
        proof {
            assert(bidi(l@[k as int]) == b);
        }
        k += 1;
    }
    is_l || !(en && an)
}

// ---------------------------------------------------------------------------
// Convert/Validate
// ---------------------------------------------------------------------------

/// Step 4 for one label, `l`. The result is `l` itself, or, for an "xn--"
/// label that decodes, what `u` holds (r.0 says which); r.1 is the error
/// flag. `pb` and `u` are scratch buffers, reused across labels.
fn convert_slice(l: &[u32], o: Options, pb: &mut Vec<u8>, u: &mut Vec<u32>) -> (r: (bool, bool))
    requires
        scalars(l@),
    ensures
        !r.0 ==> (l@, r.1) == convert(l@, o),
        r.0 ==> (final(u)@, r.1) == convert(l@, o) && scalars(final(u)@),
{
    let n = l.len();
    if !(n >= 4 && l[0] == 0x78 && l[1] == 0x6E && l[2] == HYPHEN && l[3] == HYPHEN) {
        let err = !valid_exec(l, o, o.transitional);
        return (false, err);
    }
    let ghost p = l@.skip(4);
    if n - 4 > DECODE_MAX {
        return (false, true);
    }
    *pb = Vec::with_capacity(n);
    let mut k = 4;
    while k < n
        invariant
            4 <= k <= n == l@.len(),
            scalars(l@),
            starts_xn(l@),
            n - 4 <= DECODE_MAX,
            p == l@.skip(4),
            pb@ == narrow(p.take(k - 4)),
            forall|q: int| 0 <= q < k - 4 ==> #[trigger] p[q] < 0x80,
        decreases n - k,
    {
        let c = l[k];
        if c >= 0x80 {
            assert(p[k - 4] >= 0x80);
            return (false, true);
        }
        pb.push(c as u8);
        proof {
            assert(pb@ =~= narrow(p.take(k - 3)));
        }
        k += 1;
    }
    proof {
        assert(p.take(n - 4) =~= p);
        assert(all_ascii(p));
    }
    *u = Vec::with_capacity(n);
    if !decode_into(pb.as_slice(), u) {
        return (false, true);
    }
    proof {
        lemma_decode_scalars(narrow(p));
    }
    // Decoded labels are never empty here, but checking is cheap.
    let mut ascii = true;
    let mut j = 0;
    while j < u.len()
        invariant
            j <= u@.len(),
            ascii == forall|q: int| 0 <= q < j ==> #[trigger] u@[q] < 0x80,
        decreases u@.len() - j,
    {
        if u[j] >= 0x80 {
            ascii = false;
        }
        j += 1;
    }
    let err = u.len() == 0 || ascii || !valid_exec(u.as_slice(), o, false);
    (true, err)
}

// ---------------------------------------------------------------------------
// Processing
// ---------------------------------------------------------------------------

fn find_dot(v: &Vec<u32>, p: usize) -> (r: usize)
    requires
        p <= v@.len(),
    ensures
        r == find(v@, DOT, p as int),
{
    let mut q = p;
    while q < v.len() && v[q] != DOT
        invariant
            p <= q <= v@.len(),
            find(v@, DOT, p as int) == find(v@, DOT, q as int),
        decreases v@.len() - q,
    {
        q += 1;
    }
    q
}

fn append_all<T: Copy>(out: &mut Vec<T>, u: &[T])
    ensures
        final(out)@ == old(out)@ + u@,
{
    let mut k = 0;
    while k < u.len()
        invariant
            k <= u@.len(),
            out@ == old(out)@ + u@.take(k as int),
        decreases u@.len() - k,
    {
        out.push(u[k]);
        proof {
            assert(out@ =~= old(out)@ + u@.take(k + 1));
        }
        k += 1;
    }
    proof {
        assert(u@.take(u@.len() as int) =~= u@);
    }
}

proof fn lemma_split_from_nonempty<T>(s: Seq<T>, sep: T, p: int)
    ensures
        split_from(s, sep, p).len() >= 1,
{
}

proof fn lemma_join_push<T>(ls: Seq<Seq<T>>, sep: T, i: int)
    requires
        0 <= i < ls.len(),
    ensures
        join(ls.take(i + 1), sep) == if i == 0 { ls[0] } else { join(ls.take(i), sep).push(sep) + ls[i] },
{
    assert(ls.take(i + 1).drop_last() =~= ls.take(i));
}

/// Where label `j` starts, `e` holding where each label ends.
pub open spec fn lstart(e: Seq<usize>, j: int) -> int {
    if j == 0 { 0 } else { e[j - 1] + 1 }
}

/// The labels of the result are where `e` says.
#[verifier::opaque]
pub open spec fn at_ends(out: Seq<u32>, e: Seq<usize>, conv: Seq<Seq<u32>>, i: int) -> bool {
    &&& e.len() == i
    &&& forall|j: int| 0 <= j < i ==> lstart(e, j) <= #[trigger] e[j] <= out.len()
    &&& forall|j: int| 0 <= j < i ==> out.subrange(lstart(e, j), #[trigger] e[j] as int) == conv[j]
    &&& forall|j: int| 0 <= j < i - 1 ==> #[trigger] e[j] < out.len() && out[e[j] as int] == DOT
    &&& i > 0 ==> out.len() == e[i - 1]
    &&& i == 0 ==> out.len() == 0
}

/// Processing (4), `s` being the UTF-8 encoding of `cs`.
pub fn process_exec(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>) -> (r: (Vec<u32>, bool))
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        (r.0@, r.1) == process(cs, o),
        scalars(r.0@),
{
    let (out, _ends, err) = process_labels(s, o, Ghost(cs), Vec::new());
    (out, err)
}

#[verifier::opaque]
pub open spec fn err_upto(ls: Seq<Seq<u32>>, o: Options, i: int) -> bool {
    exists|j: int| 0 <= j < i && (#[trigger] convert(ls[j], o)).1
}

#[verifier::opaque]
pub open spec fn dom_upto(conv: Seq<Seq<u32>>, i: int) -> bool {
    exists|j: int, k: int| 0 <= j < i && 0 <= k < conv[j].len() && rtl(bidi(#[trigger] conv[j][k]))
}

#[verifier::opaque]
pub open spec fn bad_upto(conv: Seq<Seq<u32>>, i: int) -> bool {
    exists|j: int| 0 <= j < i && conv[j].len() > 0 && !bidi_ok(#[trigger] conv[j])
}

proof fn lemma_flags_zero(ls: Seq<Seq<u32>>, conv: Seq<Seq<u32>>, o: Options)
    ensures
        !err_upto(ls, o, 0),
        !dom_upto(conv, 0),
        !bad_upto(conv, 0),
{
    reveal(err_upto);
    reveal(dom_upto);
    reveal(bad_upto);
}

proof fn lemma_flags_step(
    ls: Seq<Seq<u32>>,
    conv: Seq<Seq<u32>>,
    o: Options,
    i: int,
    err0: bool,
    e: bool,
    dom0: bool,
    dom: bool,
    bad0: bool,
    bad: bool,
    u: Seq<u32>,
)
    requires
        0 <= i < ls.len() == conv.len(),
        err0 == err_upto(ls, o, i),
        e == convert(ls[i], o).1,
        u == conv[i],
        o.check_bidi ==> dom0 == dom_upto(conv, i),
        o.check_bidi ==> bad0 == bad_upto(conv, i),
        o.check_bidi ==> dom == (dom0 || exists|k: int| 0 <= k < u.len() && rtl(bidi(#[trigger] u[k]))),
        o.check_bidi ==> bad == (bad0 || (u.len() > 0 && !bidi_ok(u))),
    ensures
        (err0 || e) == err_upto(ls, o, i + 1),
        o.check_bidi ==> dom == dom_upto(conv, i + 1),
        o.check_bidi ==> bad == bad_upto(conv, i + 1),
{
    reveal(err_upto);
    reveal(dom_upto);
    reveal(bad_upto);
    if e {
        assert(convert(ls[i], o).1);
    }
    if o.check_bidi {
        if dom && !dom0 {
            let k = choose|k: int| 0 <= k < u.len() && rtl(bidi(#[trigger] u[k]));
            assert(rtl(bidi(conv[i][k])));
        }
        if !dom {
            assert forall|j: int, k: int| 0 <= j < i + 1 && 0 <= k < conv[j].len() implies !rtl(
                bidi(#[trigger] conv[j][k]),
            ) by {
                if j == i {
                    assert(conv[j][k] == u[k]);
                }
            }
        }
        if bad && !bad0 {
            assert(conv[i].len() > 0 && !bidi_ok(conv[i]));
        }
    }
}

proof fn lemma_flags_final(cs: Seq<u32>, o: Options, ls: Seq<Seq<u32>>, conv: Seq<Seq<u32>>)
    requires
        ls == labels(cs, o),
        conv == converted(cs, o),
        ls.len() == conv.len(),
    ensures
        process_error(cs, o) == (err_upto(ls, o, ls.len() as int) || (o.check_bidi && dom_upto(conv, ls.len() as int)
            && bad_upto(conv, ls.len() as int))),
{
    reveal(err_upto);
    reveal(dom_upto);
    reveal(bad_upto);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_at_ends_push(out0: Seq<u32>, mid: Seq<u32>, u: Seq<u32>, e0: Seq<usize>, conv: Seq<Seq<u32>>, i: int)
    requires
        at_ends(out0, e0, conv, i),
        0 <= i < conv.len(),
        u == conv[i],
        mid == if i > 0 { out0.push(DOT) } else { out0 },
        (mid + u).len() <= usize::MAX,
    ensures
        at_ends(mid + u, e0.push((mid + u).len() as usize), conv, i + 1),
{
    reveal(at_ends);
    let out = mid + u;
    let ends = e0.push(out.len() as usize);
    let start = mid.len() as int;
    assert(out.subrange(start, out.len() as int) =~= u);
    assert forall|j: int| 0 <= j < i implies out.subrange(lstart(e0, j), #[trigger] e0[j] as int) == out0.subrange(
        lstart(e0, j),
        e0[j] as int,
    ) by {
        assert(out.subrange(lstart(e0, j), e0[j] as int) =~= out0.subrange(lstart(e0, j), e0[j] as int));
    }
    assert(lstart(ends, i) == start);
    assert forall|j: int| 0 <= j < i + 1 implies out.subrange(lstart(ends, j), #[trigger] ends[j] as int) == conv[j] by {
        if j < i {
            assert(ends[j] == e0[j]);
            assert(lstart(ends, j) == lstart(e0, j));
        }
    }
    assert forall|j: int| 0 <= j < i + 1 implies lstart(ends, j) <= #[trigger] ends[j] <= out.len() by {
        if j < i {
            assert(ends[j] == e0[j]);
            assert(lstart(ends, j) == lstart(e0, j));
        }
    }
    assert forall|j: int| 0 <= j < i implies #[trigger] ends[j] < out.len() && out[ends[j] as int] == DOT by {
        assert(ends[j] == e0[j]);
        if j < i - 1 {
            assert(out[e0[j] as int] == out0[e0[j] as int]);
        } else {
            assert(e0[j] == out0.len());
            assert(out[out0.len() as int] == mid[out0.len() as int]);
        }
    }
}

/// Processing, and where each label of the result ends.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
fn process_labels(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>, buf: Vec<u32>) -> (r: (Vec<u32>, Ghost<Seq<usize>>, bool))
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        (r.0@, r.2) == process(cs, o),
        scalars(r.0@),
        at_ends(r.0@, r.1@, converted(cs, o), converted(cs, o).len() as int),
        r.0@.len() <= usize::MAX,
{
    let m = map_utf8(s, o.transitional, Ghost(cs), buf);
    let ns = nfc_exec(m);
    let ghost ls = labels(cs, o);
    let ghost conv = converted(cs, o);
    // While no label has been decoded (`same`), the result so far is a
    // prefix of `ns`, and `out` is left empty; the first decoded label
    // copies that prefix into `out`.
    let mut out: Vec<u32> = Vec::new();
    let ghost mut go: Seq<u32> = Seq::empty();
    let mut same = true;
    let mut p: usize = 0;
    let ghost mut i: int = 0;
    let mut err = false;
    let mut dom = false;
    let mut bad = false;
    let mut first = true;
    let ghost mut ends: Seq<usize> = Seq::empty();
    let mut pb: Vec<u8> = Vec::new();
    let mut ubuf: Vec<u32> = Vec::new();
    proof {
        lemma_split_from_nonempty(ns@, DOT, 0);
        assert(ls.skip(0) =~= ls);
        lemma_flags_zero(ls, conv, o);
        reveal(at_ends);
    }
    loop
        invariant
            ns@ == nf(map_all(cs, o.transitional), true, false),
            scalars(ns@),
            ls == labels(cs, o),
            conv == converted(cs, o),
            ls == split(ns@, DOT),
            conv.len() == ls.len(),
            p <= ns@.len(),
            0 <= i < ls.len(),
            first == (i == 0),
            split_from(ns@, DOT, p as int) == ls.skip(i),
            go == join(conv.take(i), DOT),
            scalars(go),
            at_ends(go, ends, conv, i),
            same ==> go == ns@.subrange(0, if i == 0 { 0 } else { p - 1 }),
            !same ==> out@ == go,
            i > 0 ==> 1 <= p && ns@[p - 1] == DOT,
            i == 0 ==> p == 0,
            err == err_upto(ls, o, i),
            o.check_bidi ==> dom == dom_upto(conv, i),
            o.check_bidi ==> bad == bad_upto(conv, i),
        decreases ns@.len() - p,
    {
        let d = find_dot(&ns, p);
        proof {
            lemma_find(ns@, DOT, p as int);
            assert(ls.skip(i)[0] == ls[i]);
        }
        let label = vstd::slice::slice_subrange(ns.as_slice(), p, d);
        proof {
            assert(label@ == ls[i]);
            assert forall|k: int| 0 <= k < label@.len() implies is_scalar(#[trigger] label@[k]) by {
                assert(label@[k] == ns@[p + k]);
            }
        }
        let (dec, e) = convert_slice(label, o, &mut pb, &mut ubuf);
        let u: &[u32] = if dec { ubuf.as_slice() } else { label };
        proof {
            assert(conv[i] == convert(ls[i], o).0);
            assert(u@ == conv[i]);
        }
        let ghost out0 = go;
        let ghost mid = if i > 0 { go.push(DOT) } else { go };
        if same && dec {
            out = Vec::with_capacity(ns.len());
            if !first {
                append_all(&mut out, vstd::slice::slice_subrange(ns.as_slice(), 0, p));
                proof {
                    assert(ns@.subrange(0, p as int) =~= ns@.subrange(0, p - 1).push(DOT));
                }
            } else {
                proof {
                    assert(out@ =~= mid);
                }
            }
            append_all(&mut out, u);
            same = false;
        } else if !same {
            if !first {
                out.push(DOT);
            }
            append_all(&mut out, u);
        }
        proof {
            if same {
                assert(u@ == ns@.subrange(p as int, d as int));
                assert(mid =~= ns@.subrange(0, p as int));
                assert(mid + u@ =~= ns@.subrange(0, d as int));
            } else {
                assert(out@ =~= mid + u@);
            }
        }
        let ghost e0 = ends;
        let ghost el: usize = if same { d } else { out.len() };
        proof {
            ends = ends.push(el);
        }
        proof {
            lemma_at_ends_push(out0, mid, u@, e0, conv, i);
            lemma_join_push(conv, DOT, i);
            lemma_scalars_append(out0, if i > 0 { seq![DOT] } else { seq![] });
            if i > 0 {
                assert(out0.push(DOT) =~= out0 + seq![DOT]);
                lemma_scalars_append(out0 + seq![DOT], u@);
            } else {
                lemma_scalars_append(out0, u@);
                assert(out0 =~= Seq::<u32>::empty());
            }
            go = mid + u@;
        }
        let ghost err0 = err;
        let ghost dom0 = dom;
        let ghost bad0 = bad;
        if e {
            err = true;
        }
        if o.check_bidi {
            if has_rtl_exec(u) {
                dom = true;
            }
            if u.len() > 0 && !bidi_ok_exec(u) {
                bad = true;
            }
            assert(bad == (bad0 || (u@.len() > 0 && !bidi_ok(u@))));
        }
        proof {
            lemma_flags_step(ls, conv, o, i, err0, e, dom0, dom, bad0, bad, u@);
        }
        if d >= ns.len() {
            proof {
                assert(ls.skip(i).len() == 1);
                assert(ls.len() == i + 1);
                assert(conv.take(i + 1) =~= conv);
            }
            let r = err || (o.check_bidi && dom && bad);
            proof {
                lemma_flags_final(cs, o, ls, conv);
                if same {
                    assert(go =~= ns@);
                }
            }
            if same {
                return (ns, Ghost(ends), r);
            }
            return (out, Ghost(ends), r);
        }
        proof {
            assert(ls.skip(i + 1) =~= ls.skip(i).skip(1));
            assert(split_from(ns@, DOT, p as int) == seq![ns@.subrange(p as int, d as int)] + split_from(ns@, DOT, d + 1));
            assert(ls.skip(i).skip(1) =~= split_from(ns@, DOT, d + 1));
            lemma_split_from_nonempty(ns@, DOT, d + 1);
        }
        p = d + 1;
        first = false;
        proof {
            i = i + 1;
        }
    }
}

// ---------------------------------------------------------------------------
// ToASCII
// ---------------------------------------------------------------------------

/// Appends ToASCII's form of label `l`, or fails.
fn ascii_label_into(l: &[u32], res: &mut Vec<u8>) -> (r: bool)
    ensures
        r == ascii_label(l@) is Some,
        r ==> final(res)@ == old(res)@ + ascii_label(l@)->0,
{
    let n = l.len();
    let mut k = 0;
    while k < n && l[k] < 0x80
        invariant
            n == l@.len(),
            k <= n,
            forall|q: int| 0 <= q < k ==> #[trigger] l@[q] < 0x80,
        decreases n - k,
    {
        k += 1;
    }
    if k == n {
        let mut j = 0;
        while j < n
            invariant
                n == l@.len(),
                j <= n,
                res@ == old(res)@ + narrow(l@.take(j as int)),
            decreases n - j,
        {
            res.push(l[j] as u8);
            proof {
                assert(narrow(l@.take(j + 1)) =~= narrow(l@.take(j as int)).push(l@[j as int] as u8));
                assert(res@ =~= old(res)@ + narrow(l@.take(j + 1)));
            }
            j += 1;
        }
        proof {
            assert(l@.take(n as int) =~= l@);
        }
        return true;
    }
    assert(l@[k as int] >= 0x80);
    if n > ENCODE_MAX {
        return false;
    }
    let ghost r0 = res@;
    res.push(0x78);
    res.push(0x6E);
    res.push(0x2D);
    res.push(0x2D);
    let ghost r1 = res@;
    if !encode_append(l, res) {
        return false;
    }
    proof {
        assert(r1 =~= r0 + xn_prefix());
        assert(res@ =~= r0 + (xn_prefix() + encode(l@)->0));
    }
    true
}

proof fn lemma_dns(als: Seq<Seq<u8>>, res: Seq<u8>, trailing: bool, total: int, ok_before_last: bool, last_ok: bool, labels_ok: bool)
    requires
        als.len() >= 1,
        res == join(als, 0x2Eu8),
        trailing == (als.len() > 1 && als.last().len() == 0),
        total == if trailing { res.len() - 1 } else { res.len() as int },
        last_ok == (1 <= als.last().len() <= 63),
        ok_before_last == forall|q: int| 0 <= q < als.len() - 1 ==> 1 <= (#[trigger] als[q]).len() <= 63,
        labels_ok == (ok_before_last && last_ok),
    ensures
        (1 <= total <= 253 && labels_ok) == dns_length_ok(als),
{
    let n = als.len() as int;
    let ls2 = strip_root(als);
    if trailing {
        assert(als.drop_last().len() >= 1);
        assert(join(als, 0x2Eu8) == join(als.drop_last(), 0x2Eu8).push(0x2Eu8) + als.last());
        assert(join(als, 0x2Eu8) =~= join(als.drop_last(), 0x2Eu8).push(0x2Eu8));
    }
    assert(total == join(ls2, 0x2Eu8).len());
    if labels_ok {
        assert forall|i: int| 0 <= i < als.len() implies 1 <= (#[trigger] als[i]).len() <= 63 by {
            if i < n - 1 {
                assert(1 <= als[i].len() <= 63);
            }
        }
    } else if ok_before_last {
        assert(!(1 <= als[n - 1].len() <= 63));
    } else {
        let q = choose|q: int| 0 <= q < n - 1 && !(1 <= (#[trigger] als[q]).len() <= 63);
        assert(!(1 <= als[q].len() <= 63));
    }
    assert(labels_ok == labels_len_ok(als));
}

proof fn lemma_at_ends_get(out: Seq<u32>, e: Seq<usize>, conv: Seq<Seq<u32>>, n: int, j: int)
    requires
        at_ends(out, e, conv, n),
        0 <= j < n,
    ensures
        lstart(e, j) <= e[j] <= out.len(),
        out.subrange(lstart(e, j), e[j] as int) == conv[j],
        e.len() == n,
        j < n - 1 ==> e[j] < out.len() && out[e[j] as int] == DOT,
        j == n - 1 ==> e[j] == out.len(),
{
    reveal(at_ends);
}

/// ToASCII (4.2), `s` being the UTF-8 encoding of `cs`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn to_ascii_exec(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>) -> (r: Option<Vec<u8>>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r matches Some(b) ==> to_ascii(cs, o) == Some(b@),
        r is None ==> to_ascii(cs, o) is None,
{
    let mut m: Vec<u32> = Vec::new();
    let mut res: Vec<u8> = Vec::with_capacity(if s.len() < 0x1000_0000 { s.len() * 2 + 16 } else { s.len() });
    if to_ascii_into(s, o, Ghost(cs), &mut m, &mut res) {
        assert(res@ =~= Seq::<u8>::empty() + res@);
        Some(res)
    } else {
        None
    }
}

/// ToASCII (4.2), `s` being the UTF-8 encoding of `cs`, appending the
/// result to `res`. `m` is scratch storage, reused across calls: what it
/// holds before and after does not matter. On failure `res` may hold
/// part of the result.
#[verifier::spinoff_prover]
#[verifier::rlimit(120)]
pub fn to_ascii_into(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>, m: &mut Vec<u32>, res: &mut Vec<u8>) -> (r: bool)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r == to_ascii(cs, o) is Some,
        r ==> final(res)@ == old(res)@ + to_ascii(cs, o)->0,
{
    let mut buf: Vec<u32> = Vec::new();
    core::mem::swap(&mut buf, m);
    let (out, Ghost(ends), err) = process_labels(s, o, Ghost(cs), buf);
    if err {
        *m = out;
        return false;
    }
    let ghost pre = res@;
    let base = res.len();
    let ghost conv = converted(cs, o);
    let ghost als = conv.map_values(|l: Seq<u32>| ascii_label(l)->0);
    let ghost n = ends.len() as int;
    proof {
        reveal(at_ends);
        lemma_split_from_nonempty(nf(map_all(cs, o.transitional), true, false), DOT, 0);
        assert(conv.len() >= 1);
        assert(!process_error(cs, o));
    }
    proof {
        assert(res@ =~= pre + join(als.take(0), 0x2Eu8));
    }
    let mut ok_before_last = true;
    let mut last_ok = true;
    let mut last_len: usize = 0;
    // Labels are found by their dots: a label without error has none.
    let mut j: usize = 0;
    let mut start: usize = 0;
    let mut done = false;
    while !done
        invariant
            n == ends.len() == conv.len() == als.len(),
            n >= 1,
            conv == converted(cs, o),
            als == conv.map_values(|l: Seq<u32>| ascii_label(l)->0),
            at_ends(out@, ends, conv, n),
            !process_error(cs, o),
            j < n,
            j <= start <= out@.len(),
            done ==> j == n - 1,
            !done ==> start as int == lstart(ends, j as int),
            forall|q: int| 0 <= q < (if done { j + 1 } else { j as int }) ==> (#[trigger] ascii_label(conv[q])) is Some,
            res@ == pre + join(als.take(if done { j + 1 } else { j as int }), 0x2Eu8),
            base == pre.len(),
            (if done { j + 1 } else { j as int }) > 0 ==> last_len == als[(if done { j + 1 } else { j as int }) - 1].len(),
            (if done { j + 1 } else { j as int }) > 0 ==> last_ok == (1 <= als[(if done { j + 1 } else { j as int }) - 1].len() <= 63),
            ok_before_last == forall|q: int| 0 <= q < (if done { j + 1 } else { j as int }) - 1 ==> 1 <= (#[trigger] als[q]).len() <= 63,
        decreases out@.len() - start + (if done { 0int } else { 1int }),
    {
        let ghost e = ends[j as int] as int;
        proof {
            lemma_at_ends_get(out@, ends, conv, n, j as int);
            lemma_conv_no_dot(cs, o, j as int);
        }
        let d = find_dot(&out, start);
        proof {
            lemma_find(out@, DOT, start as int);
            assert forall|k: int| start <= k < e implies out@[k] != DOT by {
                assert(out@[k] == out@.subrange(start as int, e)[k - start]);
                if conv[j as int][k - start] == DOT {
                    assert(conv[j as int].contains(DOT));
                }
            }
            if d < e {
                assert(out@[d as int] == DOT);
            }
            if d > e {
                assert(e < out@.len());
                assert(out@[e] == DOT);
            }
            assert(d == e);
        }
        let l = vstd::slice::slice_subrange(out.as_slice(), start, d);
        assert(l@ == conv[j as int]);
        let ghost r0 = res@;
        if j > 0 {
            res.push(0x2E);
        }
        let before = res.len();
        if !ascii_label_into(l, res) {
            assert(ascii_label(conv[j as int]) is None);
            *m = out;
            return false;
        }
        let alen = res.len() - before;
        proof {
            assert(res@.len() == before + als[j as int].len());
            lemma_join_push(als, 0x2Eu8, j as int);
            let jn = join(als.take(j as int), 0x2Eu8);
            if j > 0 {
                assert(r0 =~= pre + jn);
                assert(pre + jn.push(0x2Eu8) + als[j as int] =~= res@);
            } else {
                assert(pre + jn + als[j as int] =~= res@);
            }
        }
        if j > 0 {
            ok_before_last = ok_before_last && last_ok;
        }
        last_ok = 1 <= alen && alen <= 63;
        last_len = alen;
        if d >= out.len() {
            proof {
                if j < n - 1 {
                    assert(e < out@.len());
                }
            }
            done = true;
        } else {
            proof {
                if j == n - 1 {
                    assert(e == out@.len());
                }
            }
            j += 1;
            proof {
                assert(lstart(ends, j as int) == ends[j - 1] + 1);
            }
            start = d + 1;
        }
    }
    proof {
        assert(als.take(n) =~= als);
        assert(!exists|i: int| 0 <= i < conv.len() && (#[trigger] ascii_label(conv[i])) is None);
    }
    if o.verify_dns_length {
        let trailing = j > 0 && last_len == 0;
        let len = res.len() - base;
        let total = if trailing { len - 1 } else { len };
        let labels_ok = ok_before_last && last_ok;
        proof {
            assert(res@.subrange(base as int, res@.len() as int) =~= join(als, 0x2Eu8));
            lemma_dns(als, join(als, 0x2Eu8), trailing, total as int, ok_before_last, last_ok, labels_ok);
        }
        if !(1 <= total && total <= 253 && labels_ok) {
            *m = out;
            return false;
        }
    }
    *m = out;
    true
}

/// A label of a domain without errors has no dot.
proof fn lemma_conv_no_dot(cs: Seq<u32>, o: Options, j: int)
    requires
        !process_error(cs, o),
        0 <= j < converted(cs, o).len(),
    ensures
        !converted(cs, o)[j].contains(DOT),
{
    let l = labels(cs, o)[j];
    assert(!convert(l, o).1);
    assert(converted(cs, o)[j] == convert(l, o).0);
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// The ASCII fast path
// ---------------------------------------------------------------------------

pub open spec fn lower1(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A { (c + 0x20) as u32 } else { c }
}

pub open spec fn lower(x: Seq<u32>) -> Seq<u32> {
    Seq::new(x.len(), |k: int| lower1(x[k]))
}

pub open spec fn no_double_hyphen(x: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < x.len() - 1 ==> !(#[trigger] x[k] == HYPHEN && x[k + 1] == HYPHEN)
}

/// The flags for which an ASCII domain name without `--` is only lowercased.
pub open spec fn fast_options(o: Options) -> bool {
    !o.check_hyphens && !o.use_std3_ascii_rules && !o.verify_dns_length
}

/// A hyphen at `x[k]` neither begins nor ends a label (as far as `x` goes).
pub open spec fn hyphen_inside(x: Seq<u32>, k: int) -> bool {
    x[k] == HYPHEN ==> k > 0 && x[k - 1] != DOT && (k + 1 < x.len() ==> x[k + 1] != DOT)
}

/// A dot at `x[k]` does not end an empty label.
pub open spec fn dot_after_label(x: Seq<u32>, k: int) -> bool {
    x[k] == DOT ==> k > 0 && x[k - 1] != DOT
}

pub open spec fn ldh_or_dot(c: u32) -> bool {
    0x61 <= c <= 0x7A || 0x30 <= c <= 0x39 || c == HYPHEN || c == DOT
}

/// The 64 characters from `x[a]` include a dot.
pub open spec fn dot_within_64(x: Seq<u32>, a: int) -> bool {
    exists|j: int| a <= j < a + 64 && #[trigger] x[j] == DOT
}

/// The conditions of `ascii_ok` that a prefix keeps.
pub open spec fn ascii_ok_prefix(x: Seq<u32>, o: Options) -> bool {
    &&& no_double_hyphen(x)
    &&& o.check_hyphens ==> forall|k: int| 0 <= k < x.len() ==> #[trigger] hyphen_inside(x, k)
    &&& o.use_std3_ascii_rules ==> forall|k: int| 0 <= k < x.len() ==> ldh_or_dot(#[trigger] x[k])
    &&& o.verify_dns_length ==> forall|k: int| 0 <= k < x.len() ==> #[trigger] dot_after_label(x, k)
    &&& o.verify_dns_length ==> forall|a: int| 0 <= a && a + 64 <= x.len() ==> #[trigger] dot_within_64(x, a)
}

/// An ASCII domain name (lowercased) that passes every check `o` turns on
/// without changing: no `--`, and per flag, no label beginning or ending
/// with a hyphen, only letters, digits and hyphens, and labels of 1 to 63
/// characters with 253 in all and no root label.
pub open spec fn ascii_ok(x: Seq<u32>, o: Options) -> bool {
    &&& ascii_ok_prefix(x, o)
    &&& o.check_hyphens ==> !(x.len() > 0 && x.last() == HYPHEN)
    &&& o.verify_dns_length ==> 1 <= x.len() <= 253 && x.last() != DOT
}

proof fn lemma_map_ascii(x: Seq<u32>, t: bool)
    requires
        all_ascii(x),
    ensures
        map_all(x, t) == lower(x),
    decreases x.len(),
{
    if x.len() > 0 {
        let c = x.last();
        assert(c < 0x80);
        lemma_map_ascii(x.drop_last(), t);
        axiom_idna_ascii(c);
        assert(map_one(c, t) =~= seq![lower1(c)]);
        assert(lower(x) =~= lower(x.drop_last()) + seq![lower1(c)]);
    } else {
        assert(lower(x) =~= Seq::<u32>::empty());
    }
}

proof fn lemma_nf_empty()
    ensures
        nf(Seq::<u32>::empty(), true, false) == Seq::<u32>::empty(),
{
    reveal_with_fuel(decomp_all, 1);
    reveal_with_fuel(reorder_from, 1);
    reveal_with_fuel(compose_from, 1);
    assert(nf(Seq::<u32>::empty(), true, false) =~= Seq::<u32>::empty());
}

proof fn lemma_nf_ascii(x: Seq<u32>)
    requires
        all_ascii(x),
    ensures
        nf(x, true, false) == x,
{
    lemma_ascii_stable(x, 0, x.len() as int, true, false);
    lemma_nf_stable_run(seq![], x, true, false);
    assert(Seq::<u32>::empty() + x =~= x);
    lemma_nf_empty();
}

pub open spec fn piece_at<T>(s: Seq<T>, l: Seq<T>, a: int) -> bool {
    0 <= a && a + l.len() <= s.len() && l == s.subrange(a, a + l.len())
}

pub open spec fn has_piece<T>(s: Seq<T>, l: Seq<T>) -> bool {
    exists|a: int| #[trigger] piece_at(s, l, a)
}

/// `l` is at `a` in `s`, with `sep` or an end of `s` on both sides.
pub open spec fn max_piece_at<T>(s: Seq<T>, l: Seq<T>, sep: T, a: int) -> bool {
    &&& piece_at(s, l, a)
    &&& a == 0 || s[a - 1] == sep
    &&& a + l.len() == s.len() || s[a + l.len()] == sep
}

pub open spec fn has_max_piece<T>(s: Seq<T>, l: Seq<T>, sep: T) -> bool {
    exists|a: int| #[trigger] max_piece_at(s, l, sep, a)
}

/// Each piece of a split is a run of `s` without `sep`.
proof fn lemma_split_pieces<T>(s: Seq<T>, sep: T, p: int)
    requires
        0 <= p <= s.len(),
        p == 0 || s[p - 1] == sep,
    ensures
        forall|i: int|
            0 <= i < split_from(s, sep, p).len() ==> #[trigger] has_piece(s, split_from(s, sep, p)[i]),
        forall|i: int|
            0 <= i < split_from(s, sep, p).len() ==> #[trigger] has_max_piece(s, split_from(s, sep, p)[i], sep),
        forall|i: int| 0 <= i < split_from(s, sep, p).len() ==> !(#[trigger] split_from(s, sep, p)[i]).contains(sep),
    decreases s.len() - p,
{
    let d = find(s, sep, p);
    lemma_find(s, sep, p);
    let ls = split_from(s, sep, p);
    if d >= s.len() {
        assert(ls[0] == s.subrange(p, s.len() as int));
        assert(piece_at(s, ls[0], p));
        assert(has_piece(s, ls[0]));
        assert(max_piece_at(s, ls[0], sep, p));
        assert(has_max_piece(s, ls[0], sep));
        assert forall|i: int| 0 <= i < ls.len() implies !(#[trigger] ls[i]).contains(sep) by {
            if ls[i].contains(sep) {
                let k = choose|k: int| 0 <= k < ls[i].len() && ls[i][k] == sep;
                assert(s[p + k] == sep);
            }
        }
    } else {
        lemma_split_pieces(s, sep, d + 1);
        let rest = split_from(s, sep, d + 1);
        assert(ls == seq![s.subrange(p, d)] + rest);
        assert forall|i: int| 0 <= i < ls.len() implies #[trigger] has_piece(s, ls[i]) by {
            if i == 0 {
                assert(ls[0] == s.subrange(p, p + ls[0].len()));
                assert(piece_at(s, ls[0], p));
            } else {
                assert(ls[i] == rest[i - 1]);
            }
        }
        assert forall|i: int| 0 <= i < ls.len() implies #[trigger] has_max_piece(s, ls[i], sep) by {
            if i == 0 {
                assert(ls[0] == s.subrange(p, p + ls[0].len()));
                assert(max_piece_at(s, ls[0], sep, p));
            } else {
                assert(ls[i] == rest[i - 1]);
            }
        }
        assert forall|i: int| 0 <= i < ls.len() implies !(#[trigger] ls[i]).contains(sep) by {
            if i == 0 {
                if ls[0].contains(sep) {
                    let k = choose|k: int| 0 <= k < ls[0].len() && ls[0][k] == sep;
                    assert(s[p + k] == sep);
                }
            } else {
                assert(ls[i] == rest[i - 1]);
            }
        }
    }
}

proof fn lemma_join_cons<T>(a: Seq<T>, rest: Seq<Seq<T>>, sep: T)
    requires
        rest.len() >= 1,
    ensures
        join(seq![a] + rest, sep) == a.push(sep) + join(rest, sep),
    decreases rest.len(),
{
    let l = seq![a] + rest;
    if rest.len() == 1 {
        assert(l.drop_last() =~= seq![a]);
        assert(join(seq![a], sep) == a);
    } else {
        assert(l.drop_last() =~= seq![a] + rest.drop_last());
        lemma_join_cons(a, rest.drop_last(), sep);
        assert(a.push(sep) + join(rest.drop_last(), sep) + seq![sep] + rest.last() =~= a.push(sep) + (join(
            rest.drop_last(),
            sep,
        ).push(sep) + rest.last()));
        assert((a.push(sep) + join(rest.drop_last(), sep)).push(sep) =~= a.push(sep) + join(rest.drop_last(), sep)
            + seq![sep]);
    }
}

proof fn lemma_join_split<T>(s: Seq<T>, sep: T, p: int)
    requires
        0 <= p <= s.len(),
    ensures
        join(split_from(s, sep, p), sep) == s.subrange(p, s.len() as int),
    decreases s.len() - p,
{
    let d = find(s, sep, p);
    lemma_find(s, sep, p);
    if d < s.len() {
        lemma_join_split(s, sep, d + 1);
        lemma_split_from_nonempty(s, sep, d + 1);
        lemma_join_cons(s.subrange(p, d), split_from(s, sep, d + 1), sep);
        assert(s.subrange(p, d).push(sep) + s.subrange(d + 1, s.len() as int) =~= s.subrange(p, s.len() as int));
    }
}

proof fn lemma_join_narrow(ls: Seq<Seq<u32>>)
    ensures
        join(ls.map_values(|l: Seq<u32>| narrow(l)), 0x2Eu8) == narrow(join(ls, DOT)),
    decreases ls.len(),
{
    let ns = ls.map_values(|l: Seq<u32>| narrow(l));
    if ls.len() == 0 {
        assert(narrow(join(ls, DOT)) =~= Seq::<u8>::empty());
    } else if ls.len() == 1 {
    } else {
        lemma_join_narrow(ls.drop_last());
        assert(ns.drop_last() =~= ls.drop_last().map_values(|l: Seq<u32>| narrow(l)));
        assert(narrow(join(ls.drop_last(), DOT).push(DOT) + ls.last()) =~= narrow(join(ls.drop_last(), DOT)).push(
            0x2Eu8,
        ) + narrow(ls.last()));
    }
}

/// An ASCII domain name without `--` is only lowercased.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_fast(cs: Seq<u32>, o: Options)
    requires
        all_ascii(cs),
        fast_options(o),
        no_double_hyphen(lower(cs)),
    ensures
        process(cs, o) == (lower(cs), false),
        to_ascii(cs, o) == Some(narrow(lower(cs))),
{
    lemma_fast_checked(cs, o);
}

/// An ASCII domain name that passes the checks `o` turns on is only
/// lowercased.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_fast_checked(cs: Seq<u32>, o: Options)
    requires
        all_ascii(cs),
        ascii_ok(lower(cs), o),
    ensures
        process(cs, o) == (lower(cs), false),
        to_ascii(cs, o) == Some(narrow(lower(cs))),
{
    let x = lower(cs);
    assert(all_ascii(x));
    lemma_map_ascii(cs, o.transitional);
    lemma_nf_ascii(x);
    let ls = labels(cs, o);
    assert(ls == split(x, DOT));
    lemma_split_pieces(x, DOT, 0);
    assert forall|i: int| 0 <= i < ls.len() implies #[trigger] convert(ls[i], o) == (ls[i], false) by {
        let l = ls[i];
        assert(has_max_piece(x, l, DOT));
        let a = choose|a: int| max_piece_at(x, l, DOT, a);
        assert(piece_at(x, l, a));
        assert(!l.contains(DOT));
        assert(all_ascii(l));
        if starts_xn(l) {
            assert(x[a + 2] == HYPHEN && x[a + 3] == HYPHEN);
        }
        if l.len() >= 4 && l[2] == HYPHEN && l[3] == HYPHEN {
            assert(x[a + 2] == HYPHEN && x[a + 3] == HYPHEN);
        }
        if o.check_hyphens && l.len() > 0 {
            assert(l[0] == x[a]);
            assert(hyphen_inside(x, a));
            let e = a + l.len() - 1;
            assert(l.last() == x[e]);
            assert(hyphen_inside(x, e));
        }
        lemma_nf_ascii(l);
        if l.len() > 0 {
            axiom_idna_ascii(l[0]);
        }
        assert forall|k: int| 0 <= k < l.len() implies status_ok(#[trigger] l[k], o.transitional, o.use_std3_ascii_rules) by {
            axiom_idna_ascii(l[k]);
            assert(l[k] == x[a + k]);
            if o.use_std3_ascii_rules {
                assert(ldh_or_dot(x[a + k]));
                assert(l.contains(l[k]));
            }
        }
        assert forall|k: int| 0 <= k < l.len() implies #[trigger] joiner_ok(l, k) by {
            assert(l[k] < 0x80);
        }
    }
    let conv = converted(cs, o);
    assert(conv =~= ls);
    assert(!bidi_domain(conv)) by {
        if bidi_domain(conv) {
            let (i, k) = choose|i: int, k: int| 0 <= i < conv.len() && 0 <= k < conv[i].len() && rtl(bidi(#[trigger] conv[i][k]));
            assert(has_piece(x, ls[i]));
            let a = choose|a: int| piece_at(x, ls[i], a);
            assert(conv[i][k] == x[a + k]);
            axiom_idna_ascii(conv[i][k]);
        }
    }
    lemma_join_split(x, DOT, 0);
    assert(x.subrange(0, x.len() as int) =~= x);
    assert forall|i: int| 0 <= i < conv.len() implies #[trigger] ascii_label(conv[i]) == Some(narrow(conv[i])) by {
        assert(has_piece(x, ls[i]));
            let a = choose|a: int| piece_at(x, ls[i], a);
        assert forall|k: int| 0 <= k < conv[i].len() implies #[trigger] conv[i][k] < 0x80 by {
            assert(conv[i][k] == x[a + k]);
        }
    }
    let als = conv.map_values(|l: Seq<u32>| ascii_label(l)->0);
    assert(als =~= conv.map_values(|l: Seq<u32>| narrow(l)));
    lemma_join_narrow(conv);
    if o.verify_dns_length {
        assert forall|i: int| 0 <= i < als.len() implies 1 <= (#[trigger] als[i]).len() <= 63 by {
            let l = ls[i];
            assert(als[i].len() == l.len());
            assert(has_max_piece(x, l, DOT));
            let a = choose|a: int| max_piece_at(x, l, DOT, a);
            assert(!l.contains(DOT));
            if l.len() == 0 {
                if a < x.len() {
                    assert(dot_after_label(x, a));
                } else {
                    assert(x.last() == x[a - 1]);
                }
            }
            if l.len() > 63 {
                assert(dot_within_64(x, a));
                let j = choose|j: int| a <= j < a + 64 && #[trigger] x[j] == DOT;
                assert(l[j - a] == x[j]);
                assert(l.contains(DOT));
            }
        }
        lemma_split_from_nonempty(x, DOT, 0);
        assert(strip_root(als) == als);
        assert(labels_len_ok(als));
    }
}

/// One step of `to_ascii_fast`'s loop: `ascii_ok_prefix` survives
/// appending `l` when the loop's checks pass.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_fast_step(w0: Seq<u32>, l: u32, prev: u32, k: int, run0: int, o: Options)
    requires
        k == w0.len(),
        k > 0 ==> prev == w0[k - 1],
        ascii_ok_prefix(w0, o),
        !(l == HYPHEN && prev == HYPHEN && k > 0),
        o.check_hyphens ==> !((l == HYPHEN && (k == 0 || prev == DOT)) || (l == DOT && k > 0 && prev == HYPHEN)),
        o.use_std3_ascii_rules ==> ldh_or_dot(l),
        o.verify_dns_length ==> !(l == DOT && (k == 0 || prev == DOT)),
        o.verify_dns_length && l != DOT ==> run0 < 63,
        0 <= run0 <= k,
        forall|j: int| k - run0 <= j < k ==> #[trigger] w0[j] != DOT,
        run0 < k ==> w0[k - run0 - 1] == DOT,
    ensures
        ascii_ok_prefix(w0.push(l), o),
{
    let w1 = w0.push(l);
    assert forall|j: int| 0 <= j < w1.len() - 1 implies !(#[trigger] w1[j] == HYPHEN && w1[j + 1] == HYPHEN) by {
        if j < k - 1 {
            assert(w1[j] == w0[j] && w1[j + 1] == w0[j + 1]);
        }
    }
    if o.check_hyphens {
        assert forall|j: int| 0 <= j < (k + 1) implies #[trigger] hyphen_inside(w1, j) by {
            if j < k {
                assert(hyphen_inside(w0, j));
                assert(w1[j] == w0[j]);
                if j > 0 {
                    assert(w1[j - 1] == w0[j - 1]);
                }
                if j + 1 < k {
                    assert(w1[j + 1] == w0[j + 1]);
                }
                if j + 1 == k {
                    assert(w0[j] == prev);
                }
            } else {
                if j > 0 {
                    assert(w1[j - 1] == prev);
                }
            }
        }
    }
    if o.use_std3_ascii_rules {
        assert forall|j: int| 0 <= j < (k + 1) implies ldh_or_dot(#[trigger] w1[j]) by {
            if j < k {
                assert(w1[j] == w0[j]);
            }
        }
    }
    if o.verify_dns_length {
        assert forall|j: int| 0 <= j < (k + 1) implies #[trigger] dot_after_label(w1, j) by {
            if j < k {
                assert(dot_after_label(w0, j));
                assert(w1[j] == w0[j]);
                if j > 0 {
                    assert(w1[j - 1] == w0[j - 1]);
                }
            } else if j > 0 {
                assert(w1[j - 1] == prev);
            }
        }
        assert forall|a: int| 0 <= a && a + 64 <= (k + 1) implies #[trigger] dot_within_64(w1, a) by {
            if a + 64 <= k {
                assert(dot_within_64(w0, a));
                let j = choose|j: int| a <= j < a + 64 && #[trigger] w0[j] == DOT;
                assert(w1[j] == DOT);
            } else if l == DOT {
                assert(w1[k] == DOT);
            } else {
                assert(run0 < k);
                let j = k - run0 - 1;
                assert(w1[j] == w0[j]);
            }
        }
    }
}

/// Whether `s` is an ASCII domain name that passes every check `o` turns
/// on, so that its ToASCII and ToUnicode results are `s` lowercased.
pub fn ascii_checked(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>) -> (r: bool)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r ==> all_ascii(cs) && widen(s@) == cs && to_ascii(cs, o) == Some(narrow(lower(cs))) && process(cs, o) == (
            lower(cs),
            false,
        ),
{
    let n = s.len();
    if o.verify_dns_length && (n == 0 || n > 253) {
        return false;
    }
    let mut prev: u8 = 0;
    // The characters since the last dot.
    let mut run: usize = 0;
    let mut k = 0;
    while k < n
        invariant
            n == s@.len(),
            k <= n,
            forall|j: int| 0 <= j < k ==> #[trigger] s@[j] < 0x80,
            k > 0 ==> prev as u32 == lower(widen(s@.take(k as int)))[k - 1],
            ascii_ok_prefix(lower(widen(s@.take(k as int))), o),
            run <= k,
            o.verify_dns_length ==> run <= 63,
            forall|j: int| k - run <= j < k ==> #[trigger] lower(widen(s@.take(k as int)))[j] != DOT,
            run < k ==> lower(widen(s@.take(k as int)))[k - run - 1] == DOT,
        decreases n - k,
    {
        let b = s[k];
        if b >= 0x80 {
            return false;
        }
        let l = if 0x41 <= b && b <= 0x5A { b + 0x20 } else { b };
        if l == 0x2D && prev == 0x2D && k > 0 {
            return false;
        }
        if o.check_hyphens && ((l == 0x2D && (k == 0 || prev == 0x2E)) || (l == 0x2E && k > 0 && prev == 0x2D)) {
            return false;
        }
        if o.use_std3_ascii_rules && !((0x61 <= l && l <= 0x7A) || (0x30 <= l && l <= 0x39) || l == 0x2D || l
            == 0x2E) {
            return false;
        }
        if o.verify_dns_length && l == 0x2E && (k == 0 || prev == 0x2E) {
            return false;
        }
        let ghost run0 = run;
        if l == 0x2E {
            run = 0;
        } else {
            if o.verify_dns_length && run >= 63 {
                return false;
            }
            run += 1;
        }
        proof {
            let x0 = lower(widen(s@.take(k as int)));
            let x1 = lower(widen(s@.take(k + 1)));
            assert(x1 =~= x0.push(l as u32));
            lemma_fast_step(x0, l as u32, prev as u32, k as int, run0 as int, o);
            assert forall|j: int| k + 1 - run <= j < k + 1 implies #[trigger] x1[j] != DOT by {
                if j < k {
                    assert(x1[j] == x0[j]);
                }
            }
            if run < k + 1 && l != 0x2E {
                assert(x1[k - run] == x0[k - run]);
            }
        }
        prev = l;
        k += 1;
    }
    proof {
        assert(s@.take(n as int) =~= s@);
        lemma_ascii_all(s@, cs);
        assert(widen(s@) =~= cs);
    }
    if n > 0 && ((o.check_hyphens && prev == 0x2D) || (o.verify_dns_length && prev == 0x2E)) {
        return false;
    }
    proof {
        let x = lower(cs);
        if n > 0 {
            assert(x.last() == prev as u32);
        }
        assert(ascii_ok(x, o));
        lemma_fast_checked(cs, o);
        assert forall|j: int| 0 <= j < cs.len() implies #[trigger] cs[j] < 0x80 by {
            assert(cs[j] == s@[j] as u32);
        }
    }
    true
}

/// `to_ascii` of an ASCII domain name that passes every check `o` turns on,
/// or `None` to take the general path.
pub fn to_ascii_fast(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>) -> (r: Option<Vec<u8>>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r matches Some(b) ==> to_ascii(cs, o) == Some(b@) && process(cs, o) == (widen(b@), false),
{
    if !ascii_checked(s, o, Ghost(cs)) {
        return None;
    }
    let n = s.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut k = 0;
    while k < n
        invariant
            n == s@.len() == cs.len(),
            k <= n,
            all_ascii(cs),
            s@ == enc(cs),
            widen(s@) == cs,
            out@ == narrow(lower(cs.take(k as int))),
        decreases n - k,
    {
        let b = s[k];
        let l = if 0x41 <= b && b <= 0x5A { b + 0x20 } else { b };
        proof {
            assert(cs[k as int] == b as u32);
            assert(lower(cs.take(k + 1)) =~= lower(cs.take(k as int)).push(lower1(b as u32)));
        }
        out.push(l);
        proof {
            assert(out@ =~= narrow(lower(cs.take(k + 1))));
        }
        k += 1;
    }
    proof {
        assert(cs.take(n as int) =~= cs);
        assert(widen(out@) =~= lower(cs));
    }
    Some(out)
}

/// Whether `s` is an ASCII domain name that is its own ToASCII and
/// ToUnicode result: no capital letters and no `--`.
pub fn ascii_unchanged(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>) -> (r: bool)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r ==> to_ascii(cs, o) == Some(s@) && process(cs, o) == (widen(s@), false),
{
    if o.check_hyphens || o.use_std3_ascii_rules || o.verify_dns_length {
        return false;
    }
    let n = s.len();
    let mut k = 0;
    while k < n
        invariant
            n == s@.len(),
            k <= n,
            forall|j: int| 0 <= j < k ==> #[trigger] s@[j] < 0x80 && !(0x41 <= s@[j] <= 0x5A),
            forall|j: int| 0 <= j < k - 1 ==> !(#[trigger] s@[j] == 0x2D && s@[j + 1] == 0x2D),
        decreases n - k,
    {
        let b = s[k];
        if b >= 0x80 || (0x41 <= b && b <= 0x5A) || (b == 0x2D && k > 0 && s[k - 1] == 0x2D) {
            return false;
        }
        k += 1;
    }
    proof {
        lemma_ascii_all(s@, cs);
        assert(lower(cs) =~= cs);
        assert(cs =~= widen(s@));
        assert(no_double_hyphen(lower(cs))) by {
            assert forall|j: int| 0 <= j < cs.len() - 1 implies !(#[trigger] lower(cs)[j] == HYPHEN && lower(cs)[j + 1]
                == HYPHEN) by {
                assert(lower(cs)[j] == s@[j] as u32);
                assert(lower(cs)[j + 1] == s@[j + 1] as u32);
            }
        }
        lemma_fast(cs, o);
        assert(narrow(cs) =~= s@);
    }
    true
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// The URL Standard's domain to ASCII
// ---------------------------------------------------------------------------

/// The URL Standard's host parser, beStrict false: "If domain is an ASCII
/// string, then set result to domain, lowercased. Otherwise, set result to
/// the result of running domain to ASCII", whose UTS #46 flags are `o`.
pub open spec fn url_domain_to_ascii(cs: Seq<u32>, o: Options) -> Option<Seq<u8>> {
    if all_ascii(cs) {
        Some(narrow(lower(cs)))
    } else {
        to_ascii(cs, o)
    }
}

pub fn url_domain_to_ascii_exec(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>) -> (r: Option<Vec<u8>>)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r matches Some(b) ==> url_domain_to_ascii(cs, o) == Some(b@),
        r is None ==> url_domain_to_ascii(cs, o) is None,
{
    let mut m: Vec<u32> = Vec::new();
    let mut out: Vec<u8> = Vec::new();
    if url_domain_to_ascii_into(s, o, Ghost(cs), &mut m, &mut out) {
        assert(out@ =~= Seq::<u8>::empty() + out@);
        Some(out)
    } else {
        None
    }
}

/// The index of the first byte of `s` that is not ASCII, or `s.len()`.
fn first_non_ascii(s: &[u8]) -> (k: usize)
    ensures
        k <= s.len(),
        forall|j: int| 0 <= j < k ==> #[trigger] s@[j] < 0x80,
        k < s.len() ==> s@[k as int] >= 0x80,
{
    let mut k = 0;
    while k < s.len() && s[k] < 0x80
        invariant
            k <= s.len(),
            forall|j: int| 0 <= j < k ==> #[trigger] s@[j] < 0x80,
        decreases s.len() - k,
    {
        k += 1;
    }
    k
}

/// `url_domain_to_ascii_exec`, appending the result to `out` and using `m`
/// as reusable scratch storage. On failure `out` may hold part of the
/// result.
pub fn url_domain_to_ascii_into(s: &[u8], o: Options, Ghost(cs): Ghost<Seq<u32>>, m: &mut Vec<u32>, out: &mut Vec<u8>) -> (r: bool)
    requires
        scalars(cs),
        s@ == enc(cs),
    ensures
        r == url_domain_to_ascii(cs, o) is Some,
        r ==> final(out)@ == old(out)@ + url_domain_to_ascii(cs, o)->0,
{
    let n = s.len();
    // Find a non-ASCII byte first: an ASCII domain needs no scratch.
    let k = first_non_ascii(s);
    if k < n {
        proof {
            lemma_non_ascii(s@, cs, k as int);
        }
        let ok = to_ascii_into(s, o, Ghost(cs), m, out);
        assert(url_domain_to_ascii(cs, o) == to_ascii(cs, o));
        return ok;
    }
    let ghost pre = out@;
    out.reserve(n);
    let mut k = 0;
    while k < n
        invariant
            n == s@.len(),
            k <= n,
            forall|j: int| 0 <= j < n ==> #[trigger] s@[j] < 0x80,
            out@ == pre + narrow(lower(widen(s@.take(k as int)))),
            pre == old(out)@,
            scalars(cs),
            s@ == enc(cs),
        decreases n - k,
    {
        let b = s[k];
        out.push(if 0x41 <= b && b <= 0x5A { b + 0x20 } else { b });
        proof {
            assert(lower(widen(s@.take(k + 1))) =~= lower(widen(s@.take(k as int))).push(lower1(b as u32)));
            assert(out@ =~= pre + narrow(lower(widen(s@.take(k + 1)))));
        }
        k += 1;
    }
    proof {
        assert(s@.take(n as int) =~= s@);
        lemma_ascii_all(s@, cs);
        assert(widen(s@) =~= cs);
        assert(all_ascii(cs));
        assert(url_domain_to_ascii(cs, o) == Some(narrow(lower(cs))));
        assert(out@ == pre + narrow(lower(cs)));
    }
    true
}

/// UTF-8 with a non-ASCII byte encodes a non-ASCII character.
proof fn lemma_non_ascii(s: Seq<u8>, cs: Seq<u32>, k: int)
    requires
        scalars(cs),
        s == enc(cs),
        0 <= k < s.len(),
        s[k] >= 0x80,
    ensures
        !all_ascii(cs),
{
    if all_ascii(cs) {
        assert(enc(cs) == narrow(cs)) by {
            lemma_enc_ascii(cs);
        }
        assert(s[k] == cs[k] as u8);
    }
}

proof fn lemma_enc_ascii(cs: Seq<u32>)
    requires
        all_ascii(cs),
    ensures
        enc(cs) == narrow(cs),
    decreases cs.len(),
{
    if cs.len() > 0 {
        lemma_enc_ascii(cs.drop_last());
        assert(cs.last() < 0x80);
        assert(utf8_encode(cs.last()) =~= seq![cs.last() as u8]);
        assert(narrow(cs) =~= narrow(cs.drop_last()) + seq![cs.last() as u8]);
    } else {
        assert(narrow(cs) =~= Seq::<u8>::empty());
    }
}

} // verus!
