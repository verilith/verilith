//! Verified code for `pe_spec`: flattening the DTD. Each function is
//! proven to return exactly what the spec function of the same name
//! (without `ex_`) returns.
use crate::chars::*;
use crate::dtd::*;
use crate::enc::*;
use crate::ent::ex_repl;
use crate::lex::*;
use crate::content::ex_element;
use crate::pe_spec::*;
use crate::spec::*;
use crate::tape::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The loader
// ---------------------------------------------------------------------------

/// What reads external entities: the caller's function from (the URI of
/// the entity holding the declaration, the system identifier, the public
/// identifier) to the entity's bytes and its URI. Each one is asked for
/// once and its answer kept, so the answers are a function of the
/// question, `load_model`. Trusted: that is all that is known of it.
#[verifier::external_body]
pub struct Loader {
    f: Box<dyn FnMut(&[u8], &[u8], &[u8]) -> Option<(Vec<u8>, Vec<u8>)>>,
    cache: Vec<((Vec<u8>, Vec<u8>, Vec<u8>), Option<(Vec<u8>, Vec<u8>)>)>,
    /// How many entities were read, and how many bytes in all.
    pub(crate) count: usize,
    pub(crate) bytes: usize,
    /// Where in the flattened text each parameter entity's text begins
    /// (its name and base URI) and ends (`None`): for reporting, as no
    /// proof rests on it.
    pub(crate) trace: Vec<(usize, Option<Vec<u8>>, Vec<u8>)>,
    /// The parameter entities whose text is being read, outermost first,
    /// and the one being fetched (for `open_entities`).
    open: Vec<Vec<u8>>,
    fetching: Vec<u8>,
}

/// The loader's answers.
pub uninterp spec fn load_model(l: &Loader) -> LoadFn;

impl Loader {
    /// How many entities the loader has read: for `reach`'s limit only.
    /// Trusted to return a number; nothing is assumed of it.
    #[verifier::external_body]
    pub fn count(&self) -> usize {
        self.count
    }

    /// How many bytes of entities the loader has read: for `reach`'s
    /// limit only. Trusted to return a number; nothing is assumed of it.
    #[verifier::external_body]
    pub fn bytes(&self) -> usize {
        self.bytes
    }

    /// The answer for (base, system identifier, public identifier).
    #[verifier::external_body]
    pub fn fetch(&mut self, base: &[u8], sys: &[u8], pubid: &[u8]) -> (r: Option<(Vec<u8>, Vec<u8>)>)
        ensures
            load_model(final(self)) == load_model(old(self)),
            match (load_model(old(self)))(base@, sys@, pubid@) {
                Some((b, u)) => r matches Some((x, y)) && x@ == b && y@ == u,
                None => r is None,
            },
    {
        let key = (base.to_vec(), sys.to_vec(), pubid.to_vec());
        if let Some((_, v)) = self.cache.iter().find(|(k, _)| *k == key) {
            return v.clone();
        }
        let mut names = self.open.clone();
        names.push(std::mem::take(&mut self.fetching));
        let prev = OPEN.with(|o| o.replace(names));
        let v = (self.f)(base, sys, pubid);
        OPEN.with(|o| o.replace(prev));
        if let Some((b, _)) = &v {
            self.count += 1;
            self.bytes += b.len();
        }
        self.cache.push((key, v.clone()));
        v
    }

    /// Notes that the text of the entity named `t[a..b]` (the external
    /// subset if empty), whose base URI is `base`, begins at `pos` (after
    /// a space unless `lit`).
    #[verifier::external_body]
    pub fn note_push(&mut self, pos: usize, lit: bool, t: &[u8], a: usize, b: usize, base: &[u8])
        ensures
            load_model(final(self)) == load_model(old(self)),
    {
        let pos = if lit { pos } else { pos + 1 };
        let name = t.get(a..b).unwrap_or(&[]).to_vec();
        self.open.push(name.clone());
        self.trace.push((pos, Some(name), base.to_vec()));
    }

    /// Notes that the parameter entity named `t[a..b]` is fetched next.
    #[verifier::external_body]
    pub fn note_fetch(&mut self, t: &[u8], a: usize, b: usize)
        ensures
            load_model(final(self)) == load_model(old(self)),
    {
        self.fetching = t.get(a..b).unwrap_or(&[]).to_vec();
    }

    /// Notes that the text of the innermost entity ends at `pos`.
    #[verifier::external_body]
    pub fn note_pop(&mut self, pos: usize)
        ensures
            load_model(final(self)) == load_model(old(self)),
    {
        self.open.pop();
        self.trace.push((pos, None, Vec::new()));
    }
}

/// The loader's answers, or none without one.
pub open spec fn ldm(o: &Option<Loader>) -> LoadFn {
    match o {
        Some(l) => load_model(l),
        None => |a: Seq<u8>, b: Seq<u8>, c: Seq<u8>| None::<(Seq<u8>, Seq<u8>)>,
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// A copy of `s`.
pub fn dup(s: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == s@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s@.len(),
            v@ == s@.subrange(0, i as int),
        decreases s@.len() - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof {
            assert(v@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    v
}

/// `s[a..b]`, copied.
pub fn dup_range(s: &[u8], a: usize, b: usize) -> (r: Vec<u8>)
    requires
        a <= b <= s@.len(),
    ensures
        r@ == s@.subrange(a as int, b as int),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = a;
    while i < b
        invariant
            a <= i <= b <= s@.len(),
            v@ == s@.subrange(a as int, i as int),
        decreases b - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof {
            assert(v@ =~= s@.subrange(a as int, i as int));
        }
    }
    v
}

/// Append `s[a..b]` to `out`.
pub fn append(out: &mut Vec<u8>, s: &[u8], a: usize, b: usize)
    requires
        a <= b <= s@.len(),
    ensures
        final(out)@ == old(out)@ + s@.subrange(a as int, b as int),
{
    let mut i: usize = a;
    proof {
        assert(out@ =~= old(out)@ + s@.subrange(a as int, i as int));
    }
    while i < b
        invariant
            a <= i <= b <= s@.len(),
            out@ == old(out)@ + s@.subrange(a as int, i as int),
        decreases b - i,
    {
        out.push(s[i]);
        i = i + 1;
        proof {
            assert(out@ =~= old(out)@ + s@.subrange(a as int, i as int));
        }
    }
}

/// Whether `x == y`.
pub fn bytes_eq(x: &[u8], y: &[u8]) -> (r: bool)
    ensures
        r == (x@ == y@),
{
    if x.len() != y.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < x.len()
        invariant
            x@.len() == y@.len(),
            i <= x@.len(),
            x@.subrange(0, i as int) == y@.subrange(0, i as int),
        decreases x@.len() - i,
    {
        if x[i] != y[i] {
            proof {
                assert(x@[i as int] != y@[i as int]);
            }
            return false;
        }
        i = i + 1;
        proof {
            assert(x@.subrange(0, i as int) =~= x@.subrange(0, (i - 1) as int).push(x@[i - 1]));
            assert(y@.subrange(0, i as int) =~= y@.subrange(0, (i - 1) as int).push(y@[i - 1]));
        }
    }
    proof {
        assert(x@ =~= x@.subrange(0, x@.len() as int));
        assert(y@ =~= y@.subrange(0, y@.len() as int));
    }
    true
}

/// Whether `x == t[a..b]`.
pub fn range_eq(x: &[u8], t: &[u8], a: usize, b: usize) -> (r: bool)
    requires
        a <= b <= t@.len(),
    ensures
        r == (x@ == t@.subrange(a as int, b as int)),
{
    if x.len() != b - a {
        return false;
    }
    let mut k: usize = 0;
    while k < x.len()
        invariant
            x@.len() == b - a,
            a <= b <= t@.len(),
            k <= x@.len(),
            x@.subrange(0, k as int) == t@.subrange(a as int, a + k),
        decreases x@.len() - k,
    {
        if x[k] != t[a + k] {
            proof {
                assert(x@[k as int] != t@.subrange(a as int, b as int)[k as int]);
            }
            return false;
        }
        k = k + 1;
        proof {
            assert(x@.subrange(0, k as int) =~= x@.subrange(0, (k - 1) as int).push(x@[k - 1]));
            assert(t@.subrange(a as int, a + k) =~= t@.subrange(a as int, a + k - 1).push(t@[a + k - 1]));
        }
    }
    proof {
        assert(x@ =~= x@.subrange(0, x@.len() as int));
    }
    true
}

/// `pe_ref_at`.
pub fn ex_pe_ref_at(t: &[u8], i: usize) -> (r: Option<usize>)
    requires
        i < t@.len(),
    ensures
        match pe_ref_at(t@, i as int) {
            Some(n) => r matches Some(x) && x == n && i + 1 < n < t@.len(),
            None => r is None,
        },
{
    if t[i] != 0x25 {
        return None;
    }
    let n = ex_name_end(t, i + 1);
    if n > i + 1 && ex_byte_is(t, n, 0x3B) {
        Some(n)
    } else {
        None
    }
}

/// `bom_end`.
pub fn ex_bom_end(b: &[u8]) -> (r: usize)
    ensures
        r == bom_end(b@),
        r <= b@.len(),
{
    let n = b.len();
    if n >= 3 && b[0] == 0xEF && b[1] == 0xBB && b[2] == 0xBF {
        proof {
            assert(b@.subrange(0, 3) =~= seq![0xEFu8, 0xBB, 0xBF]);
        }
        3
    } else {
        proof {
            if n >= 3 {
                assert(b@.subrange(0, 3)[0] == b@[0]);
                assert(b@.subrange(0, 3)[1] == b@[1]);
                assert(b@.subrange(0, 3)[2] == b@[2]);
            }
        }
        0
    }
}

// ---------------------------------------------------------------------------
// External parsed entities
// ---------------------------------------------------------------------------

/// `ext_declared_enc`.
pub fn ex_ext_declared_enc(b: &[u8]) -> (r: Option<(usize, usize)>)
    requires
        b@.len() <= isize::MAX,
    ensures
        match ext_declared_enc(b@) {
            Some((x, y)) => r matches Some((p, q)) && p == x && q == y && x <= y <= b@.len(),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let n = b.len();
    let p0 = ex_bom_end(b);
    if !(ex_has_lit(b, p0, &L_XMLDECL) && p0 + 5 < n && ex_is_ws(b[p0 + 5])) {
        return None;
    }
    let v = match ex_version_info(b, p0 + 5) {
        Some((v, _, _)) => v,
        None => p0 + 5,
    };
    let j = ex_ws_end(b, v);
    if j > v && ex_has_lit(b, j, &L_ENCODING) {
        match ex_enc_span(b, j) {
            Some((_, x, y)) => Some((x, y)),
            None => None,
        }
    } else {
        None
    }
}

/// `ext_enc`.
pub fn ex_ext_enc(b: &[u8]) -> (r: Enc)
    requires
        b@.len() <= isize::MAX,
    ensures
        r == ext_enc(b@),
{
    if ex_has2(b, 0, 0xFE, 0xFF) || ex_has2(b, 0, 0xFF, 0xFE) {
        return Enc::Utf16;
    }
    proof {
        lemma_enc_lits();
    }
    match ex_ext_declared_enc(b) {
        Some((x, y)) => if ex_ci_eq(b, x, y, &L_LATIN1) {
            Enc::Latin1
        } else if ex_ci_eq(b, x, y, &L_ASCII) {
            Enc::Ascii
        } else {
            Enc::Utf8
        },
        None => Enc::Utf8,
    }
}

/// `decode_as`: `None` when it is not text in `enc`, and the text itself
/// when it is UTF-8 already.
pub fn ex_decode_as(b: &[u8], enc: Enc) -> (r: Option<Option<Vec<u8>>>)
    requires
        b@.len() <= isize::MAX,
        b@.len() > 0,
    ensures
        match decode_as(b@, enc) {
            Some(u) => r matches Some(x) && match x {
                Some(v) => v@ == u,
                None => u == b@,
            },
            None => r is None,
        },
{
    match enc {
        Enc::Utf16 => {
            let le = b[0] == 0xFF;
            match ex_utf16_dec(b, le) {
                Some(v) => Some(Some(v)),
                None => None,
            }
        },
        Enc::Latin1 => Some(Some(ex_latin1_dec(b))),
        Enc::Ascii => {
            let mut k: usize = 0;
            while k < b.len()
                invariant
                    k <= b@.len(),
                    enc == Enc::Ascii,
                    forall|q: int| 0 <= q < k ==> b@[q] < 0x80,
                decreases b@.len() - k,
            {
                if b[k] >= 0x80 {
                    proof {
                        assert(b@[k as int] >= 0x80);
                        assert(!(forall|q: int| 0 <= q < b@.len() ==> b@[q] < 0x80));
                    }
                    return None;
                }
                k = k + 1;
            }
            Some(None)
        },
        Enc::Utf8 => Some(None),
    }
}

/// `text_decl`.
pub fn ex_text_decl(t: &[u8], enc: Enc) -> (r: Option<usize>)
    requires
        t@.len() <= isize::MAX,
        t@.len() <= MAX_POS,
    ensures
        match text_decl(t@, enc) {
            Some(p) => r matches Some(x) && x == p && p <= t@.len(),
            None => r is None,
        },
{
    proof {
        lemma_lits();
    }
    let n = t.len();
    let p0 = ex_bom_end(t);
    if !(ex_has_lit(t, p0, &L_XMLDECL) && p0 + 5 < n && ex_is_ws(t[p0 + 5])) {
        return Some(p0);
    }
    let j0 = ex_ws_end(t, p0 + 5);
    let v = if ex_has_lit(t, j0, &L_VERSION) {
        match ex_version_info(t, p0 + 5) {
            Some((v, a, b)) => if b == a + 3 && t[a + 2] == 0x30 {
                v
            } else {
                return None;
            },
            None => {
                return None;
            },
        }
    } else {
        p0 + 5
    };
    let j = ex_ws_end(t, v);
    if !(j > v && ex_has_lit(t, j, &L_ENCODING)) {
        return None;
    }
    match ex_encoding_decl(t, j, enc) {
        Some((e, _, _)) => {
            let m = ex_ws_end(t, e);
            if ex_has2(t, m, 0x3F, 0x3E) {
                proof {
                    assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
                }
                Some(m + 2)
            } else {
                proof {
                    assert(lit_pi_end() =~= seq![0x3Fu8, 0x3E]);
                }
                None
            }
        },
        None => None,
    }
}

/// `ext_text`.
pub fn ex_ext_text(b: Vec<u8>) -> (r: Option<(Vec<u8>, usize)>)
    ensures
        match ext_text(b@) {
            Some((t, p)) => r matches Some((x, q)) && x@ == t && q == p && p <= t.len(),
            None => r is None,
        },
        r matches Some((x, q)) ==> q <= x@.len() <= MAX_POS,
{
    if b.len() == 0 {
        return Some((b, 0));
    }
    if b.len() as u64 > MAX_POS {
        return None;
    }
    slice_len_bound(b.as_slice());
    let enc = ex_ext_enc(b.as_slice());
    let t: Vec<u8> = match ex_decode_as(b.as_slice(), enc) {
        None => {
            return None;
        },
        Some(Some(v)) => v,
        Some(None) => b,
    };
    slice_len_bound(t.as_slice());
    if t.len() as u64 > MAX_POS {
        return None;
    }
    if !ex_doc_chars(t.as_slice()) {
        return None;
    }
    match ex_text_decl(t.as_slice(), enc) {
        Some(p) => Some((t, p)),
        None => None,
    }
}


// ---------------------------------------------------------------------------
// The state
// ---------------------------------------------------------------------------

/// `Frame` (`pe` is `NO_PE` for none).
pub struct XFrame {
    /// The text being read.
    pub text: Vec<u8>,
    /// Where reading is in `text`.
    pub pos: usize,
    /// External text (see `Frame::ext`).
    pub ext: bool,
    /// The parameter entity whose replacement text this is (an index into `XFl::pes`), or `NO_PE`.
    pub pe: usize,
    /// Included in a literal (§4.4.5).
    pub lit: bool,
    /// Referred to between declarations: it must end between declarations.
    pub sep: bool,
    /// The URI of the external entity the text is in ("" for the document).
    pub base: Vec<u8>,
}

/// `XFrame::pe` for a text that is no parameter entity's replacement text.
pub const NO_PE: usize = usize::MAX;

pub open spec fn pe_int(p: usize) -> int {
    if p == NO_PE {
        -1
    } else {
        p as int
    }
}

pub open spec fn fview(f: XFrame) -> Frame {
    Frame { text: f.text@, pos: f.pos as int, ext: f.ext, pe: pe_int(f.pe), lit: f.lit, sep: f.sep, base: f.base@ }
}

pub open spec fn frames_view(v: Seq<XFrame>) -> Seq<Frame> {
    Seq::new(v.len(), |i: int| fview(v[i]))
}

/// `Mode`: what is being read.
pub enum XMode {
    /// Between declarations.
    Sep,
    /// In a comment.
    Comment,
    /// In a processing instruction.
    Pi,
    /// In a markup declaration (see `Mode::Decl`).
    Decl {
        /// Where the declaration begins in the output.
        start: usize,
        /// The quote of the literal being read (0 outside literals).
        q: u8,
        /// The literal being read is an entity value.
        ev: bool,
        /// How many frames were open when the literal began.
        ld: usize,
        /// The URI of the entity the declaration is in.
        base: Vec<u8>,
    },
    /// In the keyword of a conditional section.
    Cond {
        /// Where the section begins in the output.
        start: usize,
    },
    /// In an ignored section.
    Ignore {
        /// How many sections deep.
        depth: usize,
    },
}

pub open spec fn mview(m: XMode) -> Mode {
    match m {
        XMode::Sep => Mode::Sep,
        XMode::Comment => Mode::Comment,
        XMode::Pi => Mode::Pi,
        XMode::Decl { start, q, ev, ld, base } => Mode::Decl {
            start: start as int,
            q,
            ev,
            ld: ld as int,
            base: base@,
        },
        XMode::Cond { start } => Mode::Cond { start: start as int },
        XMode::Ignore { depth } => Mode::Ignore { depth: depth as int },
    }
}

/// `PeDef`: a processed parameter entity declaration.
pub struct XPe {
    /// The entity's name.
    pub name: Vec<u8>,
    /// Internal (with replacement text `rt`) rather than external.
    pub internal: bool,
    /// The replacement text of an internal entity.
    pub rt: Vec<u8>,
    /// The system identifier of an external entity.
    pub sys: Vec<u8>,
    /// The public identifier of an external entity.
    pub pubid: Vec<u8>,
    /// The URI of the entity the declaration is in.
    pub base: Vec<u8>,
}

pub open spec fn pview(p: XPe) -> PeDef {
    PeDef { name: p.name@, internal: p.internal, rt: p.rt@, sys: p.sys@, pubid: p.pubid@, base: p.base@ }
}

pub open spec fn pes_view(v: Seq<XPe>) -> Seq<PeDef> {
    Seq::new(v.len(), |i: int| pview(v[i]))
}

/// `Fl`: the state of flattening a DTD.
pub struct XFl {
    /// The texts being read, innermost last.
    pub frames: Vec<XFrame>,
    /// The flattened DTD so far.
    pub out: Vec<u8>,
    /// What is being read.
    pub mode: XMode,
    /// The parameter entities declared so far.
    pub pes: Vec<XPe>,
    /// A parameter entity that was not read was referred to, in a document
    /// that is not standalone: nothing more is processed (§5.1).
    pub stop: bool,
    /// Open INCLUDE sections.
    pub incl: usize,
    /// The external subset is still to be read.
    pub ext_todo: bool,
}

pub open spec fn xview(x: &XFl) -> Fl {
    Fl {
        frames: frames_view(x.frames@),
        out: x.out@,
        mode: mview(x.mode),
        pes: pes_view(x.pes@),
        stop: x.stop,
        incl: x.incl as int,
        ext_todo: x.ext_todo,
    }
}

/// Positions are in range, and the counts have room to grow by one.
pub open spec fn wf(x: &XFl) -> bool {
    &&& forall|i: int| 0 <= i < x.frames@.len() ==> #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len()
    &&& x.out@.len() < MAX_POS
    &&& match x.mode {
        XMode::Decl { start, .. } => start <= x.out@.len(),
        XMode::Cond { start } => start <= x.out@.len(),
        XMode::Ignore { depth } => depth < usize::MAX,
        _ => true,
    }
    &&& x.pes@.len() < usize::MAX
    &&& x.incl < usize::MAX
    &&& x.frames@.len() < usize::MAX
}

/// `wf`, without the room to grow: what a step leaves.
pub open spec fn wf0(x: &XFl) -> bool {
    &&& forall|i: int| 0 <= i < x.frames@.len() ==> #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len()
    &&& match x.mode {
        XMode::Decl { start, .. } => start <= x.out@.len(),
        XMode::Cond { start } => start <= x.out@.len(),
        _ => true,
    }
}

/// How many of the counts a step may add one to.
pub open spec fn counts(x: &XFl) -> int {
    let d = match x.mode {
        XMode::Ignore { depth } => depth as int,
        _ => 0,
    };
    vstd::math::max(vstd::math::max(x.pes@.len() as int, x.incl as int), vstd::math::max(x.frames@.len() as int, d))
}

/// `Cfg`: what does not change while flattening.
pub struct XCfg {
    /// The document is standalone.
    pub sa: bool,
    /// External entities are loaded.
    pub load: bool,
    /// The document type declaration has an external identifier.
    pub has_ext: bool,
    /// The external subset's system identifier.
    pub ext_sys: Vec<u8>,
    /// The external subset's public identifier.
    pub ext_pub: Vec<u8>,
}

pub open spec fn cfg_view(c: &XCfg, ld: &Loader) -> Cfg {
    Cfg { sa: c.sa, load: c.load, ld: load_model(ld), has_ext: c.has_ext, ext_sys: c.ext_sys@, ext_pub: c.ext_pub@ }
}

/// The executable result `r` of a step (0 next, 1 done, 2 bad) is `s`.
pub open spec fn res_ok(r: u8, x: &XFl, s: Step) -> bool {
    match s {
        Step::Next(s2) => r == 0 && xview(x) == s2,
        Step::Done(o) => r == 1 && x.out@ == o,
        Step::Bad => r == 2,
    }
}

// ---------------------------------------------------------------------------
// Moving through the text
// ---------------------------------------------------------------------------

/// The top frame at `p`.
fn set_pos(frames: &mut Vec<XFrame>, p: usize)
    requires
        old(frames)@.len() > 0,
    ensures
        final(frames)@.len() == old(frames)@.len(),
        forall|i: int| 0 <= i < old(frames)@.len() - 1 ==> #[trigger] final(frames)@[i] == old(frames)@[i],
        final(frames)@.last() == (XFrame { pos: p, ..old(frames)@.last() }),
        frames_view(final(frames)@) == frames_view(old(frames)@).update(
            old(frames)@.len() - 1,
            Frame { pos: p as int, ..frames_view(old(frames)@).last() },
        ),
{
    let ghost o = frames@;
    let mut f = frames.pop().unwrap();
    f.pos = p;
    frames.push(f);
    proof {
        let n = o.len() - 1;
        assert forall|i: int| 0 <= i < n implies #[trigger] frames@[i] == o[i] by {
            assert(frames@[i] == o.drop_last()[i]);
        }
        assert(frames_view(frames@) =~= frames_view(o).update(n, Frame { pos: p as int, ..frames_view(o).last() }));
    }
}

/// `at`.
fn ex_at(x: &mut XFl, p: usize)
    requires
        old(x).frames@.len() > 0,
        wf0(old(x)),
        p <= old(x).frames@.last().text@.len(),
    ensures
        xview(final(x)) == at(xview(old(x)), p as int),
        wf0(final(x)),
        final(x).out@ == old(x).out@,
        final(x).mode == old(x).mode,
        final(x).pes@ == old(x).pes@,
        final(x).incl == old(x).incl,
        final(x).frames@.len() == old(x).frames@.len(),
{
    set_pos(&mut x.frames, p);
    proof {
        assert(forall|i: int| 0 <= i < x.frames@.len() ==> #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len()) by {
            assert forall|i: int| 0 <= i < x.frames@.len() implies #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len() by {
                if i < x.frames@.len() - 1 {
                    assert(x.frames@[i] == old(x).frames@[i]);
                }
            }
        }
    }
}

/// `copy`.
fn ex_copy(x: &mut XFl, n: usize)
    requires
        old(x).frames@.len() > 0,
        wf0(old(x)),
        old(x).frames@.last().pos + n <= old(x).frames@.last().text@.len(),
    ensures
        xview(final(x)) == copy(xview(old(x)), n as int),
        wf0(final(x)),
        final(x).mode == old(x).mode,
        final(x).pes@ == old(x).pes@,
        final(x).incl == old(x).incl,
        final(x).frames@.len() == old(x).frames@.len(),
        final(x).out@.len() == old(x).out@.len() + n,
{
    let last = x.frames.len() - 1;
    let p = x.frames[last].pos;
    let _tl = x.frames[last].text.len();
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
    }
    append(&mut x.out, x.frames[last].text.as_slice(), p, p + n);
    ex_at(x, p + n);
}

/// `copy_to`.
fn ex_copy_to(x: &mut XFl, n: usize, m: XMode)
    requires
        old(x).frames@.len() > 0,
        wf0(old(x)),
        old(x).frames@.last().pos + n <= old(x).frames@.last().text@.len(),
        match m {
            XMode::Decl { start, .. } => start <= old(x).out@.len(),
            XMode::Cond { start } => start <= old(x).out@.len(),
            _ => true,
        },
    ensures
        xview(final(x)) == copy_to(xview(old(x)), n as int, mview(m)),
        wf0(final(x)),
        final(x).mode == m,
        final(x).pes@ == old(x).pes@,
        final(x).incl == old(x).incl,
        final(x).frames@.len() == old(x).frames@.len(),
        final(x).out@.len() == old(x).out@.len() + n,
{
    ex_copy(x, n);
    x.mode = m;
}

// ---------------------------------------------------------------------------
// Lookups
// ---------------------------------------------------------------------------

proof fn lemma_find_pe(pes: Seq<PeDef>, name: Seq<u8>)
    ensures
        match find_pe(pes, name) {
            Some(j) => 0 <= j < pes.len() && pes[j].name == name && forall|i: int| 0 <= i < j ==> pes[i].name != name,
            None => forall|i: int| 0 <= i < pes.len() ==> pes[i].name != name,
        },
    decreases pes.len(),
{
    if pes.len() > 0 {
        lemma_find_pe(pes.drop_last(), name);
        assert forall|i: int| 0 <= i < pes.len() - 1 implies pes.drop_last()[i] == pes[i] by {}
    }
}

/// `find_pe` for the name `t[a..b]`.
fn ex_find_pe(pes: &Vec<XPe>, t: &[u8], a: usize, b: usize) -> (r: Option<usize>)
    requires
        a <= b <= t@.len(),
    ensures
        match find_pe(pes_view(pes@), t@.subrange(a as int, b as int)) {
            Some(j) => r matches Some(k) && k == j && k < pes@.len(),
            None => r is None,
        },
{
    let ghost name = t@.subrange(a as int, b as int);
    proof {
        lemma_find_pe(pes_view(pes@), name);
    }
    let mut i: usize = 0;
    while i < pes.len()
        invariant
            i <= pes@.len(),
            a <= b <= t@.len(),
            name == t@.subrange(a as int, b as int),
            forall|j: int| 0 <= j < i ==> pes_view(pes@)[j].name != name,
        decreases pes@.len() - i,
    {
        let same = range_eq(pes[i].name.as_slice(), t, a, b);
        if same {
            proof {
                assert(pes_view(pes@)[i as int].name == name);
                lemma_find_pe(pes_view(pes@), name);
                match find_pe(pes_view(pes@), name) {
                    Some(j) => {
                        if j < i {
                            assert(pes_view(pes@)[j].name != name);
                        }
                    },
                    None => {
                        assert(pes_view(pes@)[i as int].name != name);
                    },
                }
            }
            return Some(i);
        }
        proof {
            assert(pes_view(pes@)[i as int].name != name);
        }
        i = i + 1;
    }
    proof {
        lemma_find_pe(pes_view(pes@), name);
    }
    None
}

/// `on_stack`.
fn ex_on_stack(frames: &Vec<XFrame>, k: usize) -> (r: bool)
    requires
        k != NO_PE,
    ensures
        r == on_stack(frames_view(frames@), k as int),
{
    let mut i: usize = 0;
    while i < frames.len()
        invariant
            k != NO_PE,
            i <= frames@.len(),
            forall|j: int| 0 <= j < i ==> frames_view(frames@)[j].pe != k,
        decreases frames@.len() - i,
    {
        if frames[i].pe == k {
            proof {
                assert(frames_view(frames@)[i as int].pe == k);
            }
            return true;
        }
        i = i + 1;
    }
    false
}

proof fn lemma_first_ext(fr: Seq<Frame>)
    ensures
        0 <= first_ext(fr) <= fr.len(),
        forall|i: int| 0 <= i < first_ext(fr) ==> !(#[trigger] fr[i]).ext,
        first_ext(fr) < fr.len() ==> fr[first_ext(fr)].ext,
    decreases fr.len(),
{
    if fr.len() > 0 {
        lemma_first_ext(fr.drop_last());
        assert forall|i: int| 0 <= i < fr.len() - 1 implies fr.drop_last()[i] == fr[i] by {}
    }
}

/// `first_ext`.
fn ex_first_ext(frames: &Vec<XFrame>) -> (r: usize)
    ensures
        r == first_ext(frames_view(frames@)),
        r <= frames@.len(),
{
    proof {
        lemma_first_ext(frames_view(frames@));
    }
    let mut i: usize = 0;
    while i < frames.len()
        invariant
            i <= frames@.len(),
            forall|j: int| 0 <= j < i ==> !frames_view(frames@)[j].ext,
        decreases frames@.len() - i,
    {
        if frames[i].ext {
            proof {
                assert(frames_view(frames@)[i as int].ext);
                lemma_first_ext(frames_view(frames@));
                let k = first_ext(frames_view(frames@));
                if k < i {
                    assert(frames_view(frames@)[k].ext);
                }
                if k > i {
                    assert(!frames_view(frames@)[i as int].ext);
                }
            }
            return i;
        }
        i = i + 1;
    }
    proof {
        let k = first_ext(frames_view(frames@));
        if k < frames@.len() {
            assert(frames_view(frames@)[k].ext);
        }
    }
    i
}

/// `INCLUDE`.
pub const L_INCLUDE: [u8; 7] = [0x49, 0x4E, 0x43, 0x4C, 0x55, 0x44, 0x45];
/// `IGNORE`.
pub const L_IGNORE: [u8; 6] = [0x49, 0x47, 0x4E, 0x4F, 0x52, 0x45];
/// `<![`, which opens a conditional section.
pub const L_COND: [u8; 3] = [0x3C, 0x21, 0x5B];
/// `]]>`, which closes a conditional section.
pub const L_COND_END: [u8; 3] = [0x5D, 0x5D, 0x3E];
/// `-->`, which closes a comment.
pub const L_COMMENT_END: [u8; 3] = [0x2D, 0x2D, 0x3E];
/// `<!`, which opens a markup declaration.
pub const L_DECL: [u8; 2] = [0x3C, 0x21];
/// `<?`, which opens a processing instruction.
pub const L_PI: [u8; 2] = [0x3C, 0x3F];
/// `?>`, which closes a processing instruction.
pub const L_PI_END: [u8; 2] = [0x3F, 0x3E];

proof fn lemma_pe_lits()
    ensures
        L_INCLUDE@ == lit_include(),
        L_IGNORE@ == lit_ignore(),
        L_COND@ == lit_cond(),
        L_COND_END@ == lit_cond_end(),
        L_COMMENT_END@ == lit_comment_end(),
        L_DECL@ == lit_decl(),
        L_PI@ == lit_pi(),
        L_PI_END@ == lit_pi_end(),
{
    assert(L_INCLUDE@ =~= lit_include());
    assert(L_IGNORE@ =~= lit_ignore());
    assert(L_COND@ =~= lit_cond());
    assert(L_COND_END@ =~= lit_cond_end());
    assert(L_COMMENT_END@ =~= lit_comment_end());
    assert(L_DECL@ =~= lit_decl());
    assert(L_PI@ =~= lit_pi());
    assert(L_PI_END@ =~= lit_pi_end());
}

/// `is_ev`.
fn ex_is_ev(out: &[u8], start: usize) -> (r: bool)
    requires
        start <= out@.len() <= isize::MAX,
    ensures
        r == is_ev(out@, start as int),
{
    proof {
        lemma_lits();
    }
    if !ex_has_lit(out, start, &L_ENTITY) {
        return false;
    }
    let a = ex_ws_end(out, start + 8);
    if a == start + 8 {
        return false;
    }
    if ex_byte_is(out, a, 0x25) {
        let b = ex_ws_end(out, a + 1);
        let n = ex_name_end(out, b);
        let c = ex_ws_end(out, n);
        b > a + 1 && n > b && c > n && c == out.len()
    } else {
        let n = ex_name_end(out, a);
        let c = ex_ws_end(out, n);
        n > a && c > n && c == out.len()
    }
}

/// `cond_kw`.
fn ex_cond_kw(out: &[u8], start: usize) -> (r: u8)
    requires
        start + 3 <= out@.len() <= isize::MAX,
    ensures
        r as int == cond_kw(out@, start as int),
{
    proof {
        lemma_pe_lits();
    }
    let j = ex_ws_end(out, start + 3);
    if ex_has_lit(out, j, &L_INCLUDE) && ex_ws_end(out, j + 7) == out.len() {
        1
    } else if ex_has_lit(out, j, &L_IGNORE) && ex_ws_end(out, j + 6) == out.len() {
        2
    } else {
        0
    }
}


// ---------------------------------------------------------------------------
// Parameter entity references
// ---------------------------------------------------------------------------

/// What a step that goes on leaves: the invariant without the room to
/// grow, each count up by at most one, and the loader's answers the same.
pub open spec fn grew(x0: &XFl, x: &XFl) -> bool {
    &&& wf0(x)
    &&& counts(x) <= counts(x0) + 1
}

/// `unread`.
fn ex_unread(x: &mut XFl, sa: bool, e: usize)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        old(x).frames@.last().pos <= e <= old(x).frames@.last().text@.len(),
    ensures
        xview(final(x)) == unread(xview(old(x)), sa, e as int),
        grew(old(x), final(x)),
{
    let last = x.frames.len() - 1;
    let p = x.frames[last].pos;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
    }
    if sa {
        ex_copy(x, e - p);
        return;
    }
    let k = ex_first_ext(&x.frames);
    if k == x.frames.len() {
        ex_copy(x, e - p);
        x.stop = true;
        return;
    }
    let keep = match &x.mode {
        XMode::Decl { start, .. } => *start,
        XMode::Cond { start } => *start,
        _ => x.out.len(),
    };
    let r = dup_range(x.frames[last].text.as_slice(), p, e);
    let ghost o = x.out@;
    let ghost of = x.frames@;
    x.out.truncate(keep);
    x.out.push(0x20);
    append(&mut x.out, r.as_slice(), 0, r.len());
    x.out.push(0x20);
    x.frames.truncate(k);
    x.mode = XMode::Sep;
    x.stop = true;
    proof {
        assert(r@.subrange(0, r@.len() as int) =~= r@);
        assert(x.out@ =~= o.subrange(0, keep as int) + seq![0x20u8] + r@ + seq![0x20u8]);
        assert(frames_view(x.frames@) =~= frames_view(of).subrange(0, k as int));
        assert forall|i: int| 0 <= i < x.frames@.len() implies #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len() by {
            assert(x.frames@[i] == of[i]);
        }
    }
}

/// `push`.
fn ex_push(x: &mut XFl, t: Vec<u8>, p: usize, ext: bool, k: usize, lit: bool, sep: bool, base: Vec<u8>, e: usize)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        e <= old(x).frames@.last().text@.len(),
        p <= t@.len(),
        k != NO_PE,
    ensures
        xview(final(x)) == push(xview(old(x)), t@, p as int, ext, k as int, lit, sep, base@, e as int),
        grew(old(x), final(x)),
{
    ex_at(x, e);
    if !lit {
        x.out.push(0x20);
    }
    let ghost f1 = x.frames@;
    let nf = XFrame { text: t, pos: p, ext, pe: k, lit, sep, base };
    x.frames.push(nf);
    proof {
        assert(frames_view(x.frames@) =~= frames_view(f1).push(fview(nf)));
        assert forall|i: int| 0 <= i < x.frames@.len() implies #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len() by {
            if i < f1.len() {
                assert(x.frames@[i] == f1[i]);
            }
        }
    }
}

/// `peref`: the name ends at `n` in the top frame.
fn ex_pe_ref(x: &mut XFl, c: &XCfg, ld: &mut Loader, n: usize, lit: bool, sep: bool) -> (r: u8)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        old(x).frames@.last().pos < old(x).frames@.last().text@.len(),
        pe_ref_at(old(x).frames@.last().text@, old(x).frames@.last().pos as int) == Some(n as int),
    ensures
        res_ok(r, final(x), peref(xview(old(x)), cfg_view(c, old(ld)), n as int, lit, sep)),
        r == 0 ==> grew(old(x), final(x)),
        load_model(final(ld)) == load_model(old(ld)),
{
    let last = x.frames.len() - 1;
    let p = x.frames[last].pos;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let _tl = x.frames[last].text.len();
    let e = n + 1;
    if x.stop {
        ex_copy(x, e - p);
        return 0;
    }
    let kk = ex_find_pe(&x.pes, x.frames[last].text.as_slice(), p + 1, n);
    match kk {
        None => {
            ex_unread(x, c.sa, e);
            0
        },
        Some(k) => {
            proof {
                assert(pes_view(x.pes@)[k as int] == pview(x.pes@[k as int]));
            }
            if ex_on_stack(&x.frames, k) {
                return 2;
            }
            if x.pes[k].internal {
                let t = dup(x.pes[k].rt.as_slice());
                let b = dup(x.pes[k].base.as_slice());
                let ext = x.frames[last].ext;
                ld.note_push(x.out.len(), lit, x.frames[last].text.as_slice(), p + 1, n, b.as_slice());
                ex_push(x, t, 0, ext, k, lit, sep, b, e);
                0
            } else if !c.load {
                ex_unread(x, c.sa, e);
                0
            } else {
                ld.note_fetch(x.frames[last].text.as_slice(), p + 1, n);
                let got = ld.fetch(x.pes[k].base.as_slice(), x.pes[k].sys.as_slice(), x.pes[k].pubid.as_slice());
                match got {
                    None => {
                        ex_unread(x, c.sa, e);
                        0
                    },
                    Some((b, uri)) => match ex_ext_text(b) {
                        None => 2,
                        Some((t, q)) => {
                            ld.note_push(x.out.len(), lit, x.frames[last].text.as_slice(), p + 1, n, uri.as_slice());
                            ex_push(x, t, q, true, k, lit, sep, uri, e);
                            0
                        },
                    },
                }
            }
        },
    }
}

/// `pop`.
fn ex_pop(x: &mut XFl) -> (r: u8)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
    ensures
        res_ok(r, final(x), pop(xview(old(x)))),
        r == 0 ==> grew(old(x), final(x)),
{
    let nf = x.frames.len();
    let last = nf - 1;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let bad = match &x.mode {
        XMode::Comment => true,
        XMode::Pi => true,
        XMode::Ignore { .. } => true,
        XMode::Decl { q, ld, .. } => *q != 0 && *ld == nf,
        _ => false,
    };
    let is_sep = match &x.mode {
        XMode::Sep => true,
        _ => false,
    };
    if bad || (x.frames[last].sep && !is_sep) {
        return 2;
    }
    let ghost of = x.frames@;
    let f = x.frames.pop().unwrap();
    if f.pe != NO_PE && !f.lit {
        x.out.push(0x20);
    }
    proof {
        assert(f == of.last());
        assert(frames_view(x.frames@) =~= frames_view(of).drop_last());
        assert forall|i: int| 0 <= i < x.frames@.len() implies #[trigger] x.frames@[i].pos <= x.frames@[i].text@.len() by {
            assert(x.frames@[i] == of[i]);
        }
    }
    0
}

/// `next_root`.
fn ex_next_root(x: &mut XFl, c: &XCfg, ld: &mut Loader) -> (r: u8)
    requires
        old(x).frames@.len() == 0,
        wf(old(x)),
    ensures
        res_ok(r, final(x), next_root(xview(old(x)), cfg_view(c, old(ld)))),
        r == 0 ==> grew(old(x), final(x)),
        load_model(final(ld)) == load_model(old(ld)),
{
    if x.ext_todo {
        x.ext_todo = false;
        if c.has_ext && c.load && !x.stop {
            let empty: Vec<u8> = Vec::new();
            proof {
                assert(empty@ =~= Seq::<u8>::empty());
            }
            match ld.fetch(empty.as_slice(), c.ext_sys.as_slice(), c.ext_pub.as_slice()) {
                None => 0,
                Some((b, uri)) => match ex_ext_text(b) {
                    None => 2,
                    Some((t, p)) => {
                        ld.note_push(x.out.len(), true, empty.as_slice(), 0, 0, uri.as_slice());
                        let nf = XFrame { text: t, pos: p, ext: true, pe: NO_PE, lit: false, sep: true, base: uri };
                        x.frames.push(nf);
                        proof {
                            assert(frames_view(x.frames@) =~= seq![fview(nf)]);
                        }
                        0
                    },
                },
            }
        } else {
            0
        }
    } else {
        let is_sep = match &x.mode {
            XMode::Sep => true,
            _ => false,
        };
        if is_sep && x.incl == 0 {
            1
        } else {
            2
        }
    }
}


// ---------------------------------------------------------------------------
// The modes
// ---------------------------------------------------------------------------

/// A span of a token, as positions in `out` if it is in range.
fn span_in(t: Tok, n: usize) -> (r: Option<(usize, usize)>)
    ensures
        match r {
            Some((a, b)) => a == t.sa() && b == t.sb() && a <= b <= n,
            None => !(0 <= t.sa() <= t.sb() <= n),
        },
{
    let a = t.a48();
    let b = t.b48();
    if a <= b && b <= n as u64 {
        Some((a as usize, b as usize))
    } else {
        None
    }
}

/// `pe_def`.
fn ex_pe_def(out: &[u8], t: &Tape, base: Vec<u8>) -> (r: Option<XPe>)
    requires
        out@.len() <= isize::MAX,
        out@.len() <= MAX_POS,
    ensures
        match pe_def(out@, t@, base@) {
            Some(d) => r matches Some(p) && pview(p) == d,
            None => r is None,
        },
{
    let n = t.len();
    if n < 2 {
        return None;
    }
    let t0 = t.toks[0];
    let t1 = t.toks[1];
    proof {
        assert(t@[0] == t0@);
        assert(t@[1] == t1@);
    }
    match t0.kind {
        Kind::EntityDecl => {},
        _ => {
            return None;
        },
    }
    if t0.f == 0 {
        return None;
    }
    let (na, nb) = match span_in(t0, out.len()) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let name = dup_range(out, na, nb);
    match t1.kind {
        Kind::EntityValue => match span_in(t1, out.len()) {
            Some((va, vb)) => {
                let rt = ex_repl(out, va, vb);
                Some(XPe { name, internal: true, rt, sys: Vec::new(), pubid: Vec::new(), base })
            },
            None => None,
        },
        Kind::SysId => match span_in(t1, out.len()) {
            Some((sa, sb)) => {
                let sys = dup_range(out, sa, sb);
                let r = XPe { name, internal: false, rt: Vec::new(), sys, pubid: Vec::new(), base };
                proof {
                    assert(r.rt@ =~= Seq::<u8>::empty());
                    assert(r.pubid@ =~= Seq::<u8>::empty());
                }
                Some(r)
            },
            None => None,
        },
        Kind::PubId => {
            if n < 3 {
                return None;
            }
            let (pa, pb) = match span_in(t1, out.len()) {
                Some(x) => x,
                None => {
                    return None;
                },
            };
            let t2 = t.toks[2];
            proof {
                assert(t@[2] == t2@);
            }
            match t2.kind {
                Kind::SysId => match span_in(t2, out.len()) {
                    Some((sa, sb)) => {
                        let sys = dup_range(out, sa, sb);
                        let pubid = dup_range(out, pa, pb);
                        let r = XPe { name, internal: false, rt: Vec::new(), sys, pubid, base };
                        proof {
                            assert(r.rt@ =~= Seq::<u8>::empty());
                        }
                        Some(r)
                    },
                    None => None,
                },
                _ => None,
            }
        },
        _ => None,
    }
}

/// `end_decl`, after the `>` was copied.
fn ex_end_decl(x: &mut XFl, start: usize, base: Vec<u8>) -> (r: u8)
    requires
        wf0(old(x)),
        old(x).out@.len() <= MAX_POS,
        start <= old(x).out@.len(),
        old(x).pes@.len() < usize::MAX,
    ensures
        res_ok(r, final(x), end_decl(xview(old(x)), start as int, base@)),
        r == 0 ==> wf0(final(x)) && final(x).pes@.len() <= old(x).pes@.len() + 1 && final(x).incl == old(x).incl
            && final(x).frames@.len() == old(x).frames@.len() && final(x).mode == XMode::Sep,
{
    x.mode = XMode::Sep;
    proof {
        lemma_lits();
    }
    slice_len_bound(x.out.as_slice());
    if x.stop || !ex_has_lit(x.out.as_slice(), start, &L_ENTITY) {
        return 0;
    }
    let mut t = Tape::new();
    let mut d = XDtd { ents: Vec::new(), pe_seen: false, sa: false };
    proof {
        assert(ents_view(x.out@, d.ents@) =~= Seq::<Ent>::empty());
        assert(dtd_view(x.out@, &d) == dtd_init(false));
    }
    match ex_entity_decl(x.out.as_slice(), start, &mut t, &mut d) {
        None => 2,
        Some(e) => if e != x.out.len() {
            2
        } else {
            match ex_pe_def(x.out.as_slice(), &t, base) {
                Some(p) => {
                    let ghost op = x.pes@;
                    x.pes.push(p);
                    proof {
                        assert(pes_view(x.pes@) =~= pes_view(op).push(pview(p)));
                    }
                    0
                },
                None => 0,
            }
        },
    }
}

/// The quote `q` written as a character reference, onto `out`.
fn push_esc(out: &mut Vec<u8>, q: u8)
    ensures
        final(out)@ == old(out)@ + esc_quote(q),
{
    out.push(0x26);
    out.push(0x23);
    out.push(0x33);
    if q == 0x22 {
        out.push(0x34);
    } else {
        out.push(0x39);
    }
    out.push(0x3B);
    proof {
        assert(final(out)@ =~= old(out)@ + esc_quote(q));
    }
}

/// `step_sep`.
fn ex_step_sep(x: &mut XFl, c: &XCfg, ld: &mut Loader) -> (r: u8)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        old(x).mode == XMode::Sep,
        old(x).frames@.last().pos < old(x).frames@.last().text@.len(),
    ensures
        res_ok(r, final(x), step_sep(xview(old(x)), cfg_view(c, old(ld)))),
        r == 0 ==> grew(old(x), final(x)),
        load_model(final(ld)) == load_model(old(ld)),
{
    proof {
        lemma_lits();
        lemma_pe_lits();
    }
    let last = x.frames.len() - 1;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let i = x.frames[last].pos;
    let _tl = x.frames[last].text.len();
    let ext = x.frames[last].ext;
    match ex_pe_ref_at(x.frames[last].text.as_slice(), i) {
        Some(n) => {
            return ex_pe_ref(x, c, ld, n, false, true);
        },
        None => {},
    }
    if ex_has_lit(x.frames[last].text.as_slice(), i, &L_COMMENT) {
        ex_copy_to(x, 4, XMode::Comment);
    } else if ex_has_lit(x.frames[last].text.as_slice(), i, &L_PI) {
        ex_copy_to(x, 2, XMode::Pi);
    } else if ext && ex_has_lit(x.frames[last].text.as_slice(), i, &L_COND) {
        let st = x.out.len();
        ex_copy_to(x, 3, XMode::Cond { start: st });
    } else if ext && x.incl > 0 && ex_has_lit(x.frames[last].text.as_slice(), i, &L_COND_END) {
        ex_at(x, i + 3);
        x.incl = x.incl - 1;
    } else if ex_has_lit(x.frames[last].text.as_slice(), i, &L_DECL) {
        let st = x.out.len();
        let b = dup(x.frames[last].base.as_slice());
        ex_copy_to(x, 2, XMode::Decl { start: st, q: 0, ev: false, ld: 0, base: b });
    } else {
        ex_copy(x, 1);
    }
    0
}

/// `step_decl`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
fn ex_step_decl(x: &mut XFl, c: &XCfg, ld: &mut Loader) -> (r: u8)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        old(x).mode is Decl,
        old(x).frames@.last().pos < old(x).frames@.last().text@.len(),
    ensures
        match old(x).mode {
            XMode::Decl { start, q, ev, ld: d, base } => res_ok(
                r,
                final(x),
                step_decl(xview(old(x)), cfg_view(c, old(ld)), start as int, q, ev, d as int, base@),
            ),
            _ => false,
        },
        r == 0 ==> grew(old(x), final(x)),
        load_model(final(ld)) == load_model(old(ld)),
{
    let (start, q, ev, d, base) = match &x.mode {
        XMode::Decl { start, q, ev, ld, base } => (*start, *q, *ev, *ld, dup(base.as_slice())),
        _ => {
            return 2;
        },
    };
    let last = x.frames.len() - 1;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let i = x.frames[last].pos;
    let _tl = x.frames[last].text.len();
    let ext = x.frames[last].ext;
    let ch = x.frames[last].text[i];
    let nf = x.frames.len();
    if q == 0 {
        if ch == 0x3E {
            ex_copy(x, 1);
            return ex_end_decl(x, start, base);
        } else if ch == 0x22 || ch == 0x27 {
            slice_len_bound(x.out.as_slice());
            let e = ex_is_ev(x.out.as_slice(), start);
            ex_copy_to(x, 1, XMode::Decl { start, q: ch, ev: e, ld: nf, base });
            return 0;
        } else if ext {
            match ex_pe_ref_at(x.frames[last].text.as_slice(), i) {
                Some(n) => {
                    return ex_pe_ref(x, c, ld, n, false, false);
                },
                None => {},
            }
        }
        ex_copy(x, 1);
        0
    } else if ch == q && d == nf {
        ex_copy_to(x, 1, XMode::Decl { start, q: 0, ev: false, ld: 0, base });
        0
    } else if ch == q {
        ex_at(x, i + 1);
        push_esc(&mut x.out, q);
        0
    } else {
        if ev && ext {
            match ex_pe_ref_at(x.frames[last].text.as_slice(), i) {
                Some(n) => {
                    return ex_pe_ref(x, c, ld, n, true, false);
                },
                None => {},
            }
        }
        ex_copy(x, 1);
        0
    }
}

/// `step_cond`.
fn ex_step_cond(x: &mut XFl, c: &XCfg, ld: &mut Loader) -> (r: u8)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        old(x).mode is Cond,
        old(x).frames@.last().pos < old(x).frames@.last().text@.len(),
    ensures
        match old(x).mode {
            XMode::Cond { start } => res_ok(r, final(x), step_cond(xview(old(x)), cfg_view(c, old(ld)), start as int)),
            _ => false,
        },
        r == 0 ==> grew(old(x), final(x)),
        load_model(final(ld)) == load_model(old(ld)),
{
    let start = match &x.mode {
        XMode::Cond { start } => *start,
        _ => {
            return 2;
        },
    };
    let last = x.frames.len() - 1;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let i = x.frames[last].pos;
    let _tl = x.frames[last].text.len();
    let ch = x.frames[last].text[i];
    if ch == 0x5B {
        if x.out.len() < 3 || start > x.out.len() - 3 {
            // `<![` was copied at `start`.
            return 2;
        }
        slice_len_bound(x.out.as_slice());
        let kw = ex_cond_kw(x.out.as_slice(), start);
        if kw == 1 {
            ex_at(x, i + 1);
            x.out.truncate(start);
            x.mode = XMode::Sep;
            x.incl = x.incl + 1;
            0
        } else if kw == 2 {
            ex_at(x, i + 1);
            x.out.truncate(start);
            x.mode = XMode::Ignore { depth: 1 };
            0
        } else {
            2
        }
    } else {
        match ex_pe_ref_at(x.frames[last].text.as_slice(), i) {
            Some(n) => {
                return ex_pe_ref(x, c, ld, n, false, false);
            },
            None => {},
        }
        ex_copy(x, 1);
        0
    }
}

/// `step_ignore`.
fn ex_step_ignore(x: &mut XFl) -> (r: u8)
    requires
        old(x).frames@.len() > 0,
        wf(old(x)),
        old(x).mode is Ignore,
        old(x).frames@.last().pos < old(x).frames@.last().text@.len(),
    ensures
        match old(x).mode {
            XMode::Ignore { depth } => res_ok(r, final(x), step_ignore(xview(old(x)), depth as int)),
            _ => false,
        },
        r == 0 ==> grew(old(x), final(x)),
{
    proof {
        lemma_pe_lits();
    }
    let depth = match &x.mode {
        XMode::Ignore { depth } => *depth,
        _ => {
            return 2;
        },
    };
    let last = x.frames.len() - 1;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let i = x.frames[last].pos;
    let _tl = x.frames[last].text.len();
    if ex_has_lit(x.frames[last].text.as_slice(), i, &L_COND) {
        ex_at(x, i + 3);
        x.mode = XMode::Ignore { depth: depth + 1 };
    } else if ex_has_lit(x.frames[last].text.as_slice(), i, &L_COND_END) {
        ex_at(x, i + 3);
        x.mode = if depth <= 1 { XMode::Sep } else { XMode::Ignore { depth: depth - 1 } };
    } else {
        ex_at(x, i + 1);
    }
    0
}

/// `step`.
pub fn ex_step(x: &mut XFl, c: &XCfg, ld: &mut Loader) -> (r: u8)
    requires
        wf(old(x)),
    ensures
        res_ok(r, final(x), step(xview(old(x)), cfg_view(c, old(ld)))),
        r == 0 ==> grew(old(x), final(x)),
        load_model(final(ld)) == load_model(old(ld)),
{
    proof {
        lemma_pe_lits();
    }
    if x.frames.len() == 0 {
        return ex_next_root(x, c, ld);
    }
    let last = x.frames.len() - 1;
    proof {
        assert(x.frames@[last as int] == x.frames@.last());
        assert(fview(x.frames@[last as int]) == xview(x).frames.last());
    }
    let i = x.frames[last].pos;
    if i >= x.frames[last].text.len() {
        if x.frames[last].pe != NO_PE || x.frames[last].ext {
            ld.note_pop(x.out.len());
        }
        return ex_pop(x);
    }
    let m = match &x.mode {
        XMode::Sep => 0u8,
        XMode::Comment => 1,
        XMode::Pi => 2,
        XMode::Decl { .. } => 3,
        XMode::Cond { .. } => 4,
        XMode::Ignore { .. } => 5,
    };
    if m == 0 {
        ex_step_sep(x, c, ld)
    } else if m == 1 {
        if ex_has_lit(x.frames[last].text.as_slice(), i, &L_COMMENT_END) {
            ex_copy_to(x, 3, XMode::Sep);
        } else {
            ex_copy(x, 1);
        }
        0
    } else if m == 2 {
        if ex_has_lit(x.frames[last].text.as_slice(), i, &L_PI_END) {
            ex_copy_to(x, 2, XMode::Sep);
        } else {
            ex_copy(x, 1);
        }
        0
    } else if m == 3 {
        ex_step_decl(x, c, ld)
    } else if m == 4 {
        ex_step_cond(x, c, ld)
    } else {
        ex_step_ignore(x)
    }
}


// ---------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------

/// `run`: 0 when it ends with the flattened DTD in `x.out`, 1 not
/// well-formed, 2 out of budget.
pub fn ex_run(x: &mut XFl, c: &XCfg, ld: &mut Loader, fuel: usize) -> (r: u8)
    requires
        wf0(old(x)),
        counts(old(x)) <= 1,
        fuel < usize::MAX - 1,
    ensures
        match run(xview(old(x)), cfg_view(c, old(ld)), fuel as nat) {
            FlatRes::Ok(o) => r == 0 && final(x).out@ == o && o.len() < MAX_POS,
            FlatRes::Bad => r == 1,
            FlatRes::Limit => r == 2,
        },
        load_model(final(ld)) == load_model(old(ld)),
{
    let mut f = fuel;
    loop
        invariant
            wf0(x),
            f <= fuel < usize::MAX - 1,
            counts(x) <= 1 + (fuel - f),
            load_model(ld) == load_model(old(ld)),
            run(xview(x), cfg_view(c, ld), f as nat) == run(xview(old(x)), cfg_view(c, old(ld)), fuel as nat),
        decreases f,
    {
        if f == 0 || x.out.len() as u64 >= MAX_POS {
            return 2;
        }
        proof {
            assert(wf(x));
        }
        let r = ex_step(x, c, ld);
        proof {
            assert(cfg_view(c, ld) == cfg_view(c, old(ld)));
        }
        if r == 1 {
            return 0;
        }
        if r == 2 {
            return 1;
        }
        f = f - 1;
    }
}

/// `flat`: the flattened DTD of the internal subset `sub`.
pub fn ex_flat(sub: Vec<u8>, c: &XCfg, ld: &mut Loader, fuel: usize) -> (r: (u8, Vec<u8>))
    requires
        fuel < usize::MAX - 1,
    ensures
        match flat(sub@, cfg_view(c, old(ld)), fuel as nat) {
            FlatRes::Ok(o) => r.0 == 0 && r.1@ == o && o.len() < MAX_POS,
            FlatRes::Bad => r.0 == 1,
            FlatRes::Limit => r.0 == 2,
        },
        load_model(final(ld)) == load_model(old(ld)),
{
    let ghost sv = sub@;
    let root = XFrame { text: sub, pos: 0, ext: false, pe: NO_PE, lit: false, sep: true, base: Vec::new() };
    let mut frames: Vec<XFrame> = Vec::new();
    frames.push(root);
    let mut x = XFl {
        frames,
        out: Vec::new(),
        mode: XMode::Sep,
        pes: Vec::new(),
        stop: false,
        incl: 0,
        ext_todo: true,
    };
    proof {
        assert(frames_view(x.frames@) =~= init(sv).frames);
        assert(x.out@ =~= Seq::<u8>::empty());
        assert(pes_view(x.pes@) =~= Seq::<PeDef>::empty());
        assert(xview(&x) == init(sv));
        assert(x.frames@[0].pos <= x.frames@[0].text@.len());
    }
    let r = ex_run(&mut x, c, ld, fuel);
    (r, x.out)
}


// ---------------------------------------------------------------------------
// The document
// ---------------------------------------------------------------------------

/// `DtInfo`.
pub struct XDtInfo {
    /// The internal subset's state.
    pub d: XDtd,
    /// The document type declaration has an external identifier.
    pub ext: bool,
    /// Its system identifier.
    pub sys: Vec<u8>,
    /// Its public identifier.
    pub pubid: Vec<u8>,
    /// The span of the internal subset (the text between `[` and `]`), if there is one.
    pub sub: Option<(usize, usize)>,
}

pub open spec fn di_view(s: Seq<u8>, d: &XDtInfo) -> DtInfo {
    DtInfo {
        st: dtd_view(s, &d.d),
        ext: d.ext,
        sys: d.sys@,
        pubid: d.pubid@,
        sub: match d.sub {
            Some((a, b)) => Some((a as int, b as int)),
            None => None,
        },
    }
}

pub open spec fn di_wf(s: Seq<u8>, d: &XDtInfo) -> bool {
    &&& dtd_wf(s, &d.d)
    &&& d.d.ents@.len() <= s.len()
    &&& match d.sub {
        Some((a, b)) => a <= b <= s.len(),
        None => true,
    }
}

/// `ext_ids`.
fn ex_ext_ids(s: &[u8], t: &Tape, k: usize) -> (r: (Vec<u8>, Vec<u8>))
    ensures
        (r.0@, r.1@) == ext_ids(s@, t@, k as int),
{
    let n = t.len();
    let e0: Vec<u8> = Vec::new();
    let e1: Vec<u8> = Vec::new();
    proof {
        assert(e0@ =~= Seq::<u8>::empty());
        assert(e1@ =~= Seq::<u8>::empty());
    }
    if n > k && n - k > 1 {
        let t0 = t.toks[k];
        let t1 = t.toks[k + 1];
        proof {
            assert(t@[k as int] == t0@);
            assert(t@[k + 1] == t1@);
        }
        match (t0.kind, t1.kind) {
            (Kind::PubId, Kind::SysId) => match (span_in(t0, s.len()), span_in(t1, s.len())) {
                (Some((pa, pb)), Some((sa, sb))) => (dup_range(s, sa, sb), dup_range(s, pa, pb)),
                _ => (e0, e1),
            },
            _ => (e0, e1),
        }
    } else if n > k {
        let t0 = t.toks[k];
        proof {
            assert(t@[k as int] == t0@);
        }
        match t0.kind {
            Kind::SysId => match span_in(t0, s.len()) {
                Some((sa, sb)) => (dup_range(s, sa, sb), e1),
                None => (e0, e1),
            },
            _ => (e0, e1),
        }
    } else {
        (e0, e1)
    }
}

/// `doctype_x` at `i`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn ex_doctype_x(s: &[u8], i: usize, tape: &mut Tape, sa: bool) -> (r: Option<(usize, XDtInfo)>)
    requires
        i + 9 <= s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() <= i,
    ensures
        match doctype_x(s@, i as int, old(tape)@, sa) {
            Some((t, e, d)) => r matches Some((x, xd)) && x == e && final(tape)@ == t && di_view(s@, &xd) == d
                && di_wf(s@, &xd) && i < e <= s@.len() && t.len() <= e,
            None => r is None,
        },
{
    let j = ex_ws_end(s, i + 9);
    let n = ex_name_end(s, j);
    if j == i + 9 || n == j {
        return None;
    }
    tape.push(tok(Kind::Doctype, j, n, 0));
    let k1 = tape.len();
    let k = ex_ws_end(s, n);
    proof {
        lemma_lits();
    }
    let (e, ext) = if k > n && (ex_has_lit(s, k, &L_SYSTEM) || ex_has_lit(s, k, &L_PUBLIC)) {
        match ex_external_id(s, k, tape) {
            Some(e) => (e, true),
            None => {
                return None;
            },
        }
    } else {
        (n, false)
    };
    let (sys, pubid) = ex_ext_ids(s, tape, k1);
    let m = ex_ws_end(s, e);
    let mut d = XDtd { ents: Vec::new(), pe_seen: false, sa };
    proof {
        assert(ents_view(s@, d.ents@) =~= Seq::<Ent>::empty());
        assert(dtd_view(s@, &d) == dtd_init(sa));
    }
    if ex_byte_is(s, m, 0x5B) {
        match ex_int_subset(s, m + 1, tape, &mut d) {
            None => None,
            Some(q) => {
                let r = ex_ws_end(s, q + 1);
                if ex_byte_is(s, r, 0x3E) {
                    tape.push(tok(Kind::DoctypeEnd, 0, 0, 0));
                    Some((r + 1, XDtInfo { d, ext, sys, pubid, sub: Some((m + 1, q)) }))
                } else {
                    None
                }
            },
        }
    } else if ex_byte_is(s, m, 0x3E) {
        tape.push(tok(Kind::DoctypeEnd, 0, 0, 0));
        Some((m + 1, XDtInfo { d, ext, sys, pubid, sub: None }))
    } else {
        None
    }
}

/// `prolog_x`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn ex_prolog_x(s: &[u8], tape: &mut Tape, enc: Enc) -> (r: Option<(usize, Option<XDtInfo>)>)
    requires
        s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        old(tape)@.len() == 0,
    ensures
        match prolog_x(s@, enc) {
            Some((t, p, d)) => r matches Some((x, xd)) && x == p && final(tape)@ == t && p <= s@.len() && t.len()
                <= p && match d {
                Some(d) => xd matches Some(y) && di_view(s@, &y) == d && di_wf(s@, &y),
                None => xd is None,
            },
            None => r is None,
        },
{
    let (p1, sd) = match crate::doc::ex_decl_head(s, tape, enc) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    let p2 = match ex_misc(s, p1, tape) {
        None => {
            return None;
        },
        Some(p) => p,
    };
    proof {
        lemma_lits();
    }
    let (p3, di) = if ex_has_lit(s, p2, &L_DOCTYPE) {
        match ex_doctype_x(s, p2, tape, sd == 1) {
            Some((e, d)) => (e, Some(d)),
            None => {
                return None;
            },
        }
    } else {
        (p2, None)
    };
    let p4 = match ex_misc(s, p3, tape) {
        None => {
            return None;
        },
        Some(p) => p,
    };
    Some((p4, di))
}

/// The declarations the content is checked against: the document's own
/// (`DtdOut` over the document), or those of the flattened DTD (`text`,
/// its `tape`, and `DtdOut` over `text`).
pub enum XDtdRes {
    /// From the document's own text: the internal subset as written.
    Own(DtdOut),
    /// From the flattened DTD `text` (`]` ends it).
    Flat {
        /// The flattened DTD.
        text: Vec<u8>,
        /// Its tape.
        tape: Tape,
        /// Its declarations.
        out: DtdOut,
    },
    /// The DTD is not well-formed.
    Bad,
    /// A limit was reached (fuel, or the size of a position).
    Limit,
}

/// `flat_env`.
fn ex_flat_env(o: Vec<u8>, di: &XDtInfo, Ghost(s): Ghost<Seq<u8>>) -> (r: XDtdRes)
    requires
        o@.len() < MAX_POS,
    ensures
        match flat_env(o@, di_view(s, di)) {
            DtdRes::Flat { text, tape, env } => r matches XDtdRes::Flat { text: x, tape: t, out } && x@ == text
                && t@ == tape && out_view(x@, &out) == env && out_wf(x@, &out),
            DtdRes::Bad => r is Bad,
            _ => false,
        },
{
    let mut text = o;
    text.push(0x5D);
    slice_len_bound(text.as_slice());
    let mut tape = Tape::new();
    let mut d = XDtd { ents: Vec::new(), pe_seen: false, sa: di.d.sa };
    proof {
        assert(ents_view(text@, d.ents@) =~= Seq::<Ent>::empty());
        assert(dtd_view(text@, &d) == dtd_init(di.d.sa));
    }
    match ex_int_subset(text.as_slice(), 0, &mut tape, &mut d) {
        Some(q) => if q == text.len() - 1 {
            let out = ex_finish(text.as_slice(), d, di.ext || di.d.pe_seen);
            let ok = {
                let env = out.env(text.as_slice());
                crate::doc::ex_defaults_ok(text.as_slice(), &tape, &env)
            };
            if ok {
                XDtdRes::Flat { text, tape, out }
            } else {
                XDtdRes::Bad
            }
        } else {
            XDtdRes::Bad
        },
        None => XDtdRes::Bad,
    }
}

/// The step budget for flattening a DTD: enough for any DTD in use (each
/// step reads a byte or so), small enough that a document cannot make the
/// parser work long or the flattened DTD grow large.
pub const FLAT_FUEL: usize = 1 << 25;

/// `dtd_x`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn ex_dtd_x(s: &[u8], t: &Tape, di: Option<XDtInfo>, load: bool, ld: &mut Loader, fuel: usize) -> (r: XDtdRes)
    requires
        s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        fuel < usize::MAX - 1,
        match di {
            Some(d) => di_wf(s@, &d),
            None => true,
        },
    ensures
        match dtd_x(
            s@,
            t@,
            match di {
                Some(d) => Some(di_view(s@, &d)),
                None => None,
            },
            load,
            load_model(old(ld)),
            fuel as nat,
        ) {
            DtdRes::Own(env) => r matches XDtdRes::Own(out) && out_view(s@, &out) == env && out_wf(s@, &out),
            DtdRes::Flat { text, tape, env } => r matches XDtdRes::Flat { text: x, tape: tt, out } && x@ == text
                && tt@ == tape && out_view(x@, &out) == env && out_wf(x@, &out),
            DtdRes::Bad => r is Bad,
            DtdRes::Limit => r is Limit,
        },
        load_model(final(ld)) == load_model(old(ld)),
{
    match di {
        None => {
            let out = DtdOut::none(s);
            proof {
                assert(ents_view(s@, out.ents@) =~= Seq::<Ent>::empty());
                assert(out.oka@ =~= Seq::<bool>::empty());
                assert(out.okc@ =~= Seq::<bool>::empty());
                assert(out_view(s@, &out) == no_dtd());
            }
            let ok = {
                let env = out.env(s);
                crate::doc::ex_defaults_ok(s, t, &env)
            };
            if ok {
                XDtdRes::Own(out)
            } else {
                XDtdRes::Bad
            }
        },
        Some(d) => {
            if !(d.d.pe_seen || (load && d.ext)) {
                ex_own_env(s, t, d)
            } else {
                let sub = match d.sub {
                    Some((a, b)) => dup_range(s, a, b),
                    None => Vec::new(),
                };
                proof {
                    assert(sub@ =~= sub_text(s@, di_view(s@, &d)));
                }
                let c = XCfg { sa: d.d.sa, load, has_ext: d.ext, ext_sys: dup(d.sys.as_slice()), ext_pub: dup(d.pubid.as_slice()) };
                proof {
                    assert(cfg_view(&c, ld) == cfg_of(di_view(s@, &d), load, load_model(ld)));
                }
                let (code, o) = ex_flat(sub, &c, ld, fuel);
                if code == 0 {
                    let r = ex_flat_env(o, &d, Ghost(s@));
                    match r {
                        XDtdRes::Flat { .. } => if d.d.sa {
                            ex_own_env(s, t, d)
                        } else {
                            r
                        },
                        _ => r,
                    }
                } else if code == 1 {
                    XDtdRes::Bad
                } else {
                    XDtdRes::Limit
                }
            }
        },
    }
}

/// `own_env`.
fn ex_own_env(s: &[u8], t: &Tape, d: XDtInfo) -> (r: XDtdRes)
    requires
        s@.len() <= isize::MAX,
        s@.len() <= MAX_POS,
        di_wf(s@, &d),
    ensures
        match own_env(s@, t@, di_view(s@, &d)) {
            DtdRes::Own(env) => r matches XDtdRes::Own(out) && out_view(s@, &out) == env && out_wf(s@, &out),
            DtdRes::Bad => r is Bad,
            _ => false,
        },
{
    let ext = d.ext;
    let out = ex_finish(s, d.d, ext);
    let ok = {
        let env = out.env(s);
        crate::doc::ex_defaults_ok(s, t, &env)
    };
    if ok {
        XDtdRes::Own(out)
    } else {
        XDtdRes::Bad
    }
}

/// What `ex_doc_x` found: the declarations of a well-formed document
/// (the document's own, or a flattened DTD's), or why it is not.
pub enum XDocRes {
    /// Well-formed, with its declarations.
    Ok(XDtdRes),
    /// Not well-formed.
    Bad,
    /// A limit was reached (fuel, or the size of a position).
    Limit,
}

/// `doc_x`: whether `s` is a well-formed document, with the DTD read
/// whole where it needs to be; its tape in `tape`.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub fn ex_doc_x(s: &[u8], tape: &mut Tape, enc: Enc, load: bool, ld: &mut Loader, fuel: usize) -> (r: XDocRes)
    requires
        fuel < usize::MAX - 1,
    ensures
        s@.len() <= MAX_POS ==> match doc_x(s@, enc, load, load_model(old(ld)), fuel as nat) {
            DocRes::Ok(t, fl) => r matches XDocRes::Ok(d) && final(tape)@ == t && match fl {
                None => d matches XDtdRes::Own(out) && out_wf(s@, &out),
                Some((text, dt)) => d matches XDtdRes::Flat { text: x, tape: tt, out } && x@ == text && tt@ == dt
                    && out_wf(x@, &out),
            },
            DocRes::Bad => r is Bad,
            DocRes::Limit => r is Limit,
        },
        s@.len() > MAX_POS ==> r is Bad,
        r matches XDocRes::Ok(d) ==> final(tape)@.len() <= s@.len() && match d {
            XDtdRes::Own(out) => out_wf(s@, &out),
            XDtdRes::Flat { text, out, .. } => out_wf(text@, &out),
            _ => false,
        },
        load_model(final(ld)) == load_model(old(ld)),
{
    slice_len_bound(s);
    if s.len() as u64 > MAX_POS {
        return XDocRes::Bad;
    }
    if !ex_doc_chars(s) {
        return XDocRes::Bad;
    }
    tape.clear();
    tape.reserve(s.len() / 16);
    let (p, di) = match ex_prolog_x(s, tape, enc) {
        None => {
            return XDocRes::Bad;
        },
        Some(x) => x,
    };
    let d = ex_dtd_x(s, tape, di, load, ld, fuel);
    let e = match &d {
        XDtdRes::Own(out) => {
            let env = out.env(s);
            ex_element(s, p, tape, &env)
        },
        XDtdRes::Flat { text, out, .. } => {
            let env = out.env(text.as_slice());
            ex_element(s, p, tape, &env)
        },
        XDtdRes::Bad => {
            return XDocRes::Bad;
        },
        XDtdRes::Limit => {
            return XDocRes::Limit;
        },
    };
    let e = match e {
        None => {
            tape.fail(p);
            return XDocRes::Bad;
        },
        Some(e) => e,
    };
    match ex_misc(s, e, tape) {
        None => XDocRes::Bad,
        Some(f) => if f == s.len() {
            XDocRes::Ok(d)
        } else {
            tape.fail(f);
            XDocRes::Bad
        },
    }
}

/// `parse_x`: the text decoded to UTF-8 if it was not UTF-8 already
/// (`None` when `b` is the text), and `doc_x` of it; `None` if `b` is
/// not text in an encoding read here.
pub fn ex_parse_x(b: &[u8], tape: &mut Tape, load: bool, ld: &mut Loader, fuel: usize) -> (r: Option<
    (Option<Vec<u8>>, XDocRes),
>)
    requires
        fuel < usize::MAX - 1,
    ensures
        match parse_x(b@, load, load_model(old(ld)), fuel as nat) {
            Some((u, d)) => r matches Some((x, xd)) && (match x {
                Some(v) => v@ == u,
                None => u == b@,
            }) && (u.len() <= MAX_POS ==> match d {
                DocRes::Ok(t, _) => xd is Ok && final(tape)@ == t,
                DocRes::Bad => xd is Bad,
                DocRes::Limit => xd is Limit,
            }) && (u.len() > MAX_POS ==> xd is Bad) && (xd matches XDocRes::Ok(dd) ==> final(tape)@.len() <= u.len()
                && (match dd {
                XDtdRes::Own(out) => out_wf(u, &out),
                XDtdRes::Flat { text, out, .. } => out_wf(text@, &out),
                _ => false,
            })),
            None => r is None,
        },
        load_model(final(ld)) == load_model(old(ld)),
{
    slice_len_bound(b);
    let enc = ex_input_enc(b);
    match ex_decode_input(b, enc) {
        None => None,
        Some(None) => {
            let d = ex_doc_x(b, tape, enc, load, ld, fuel);
            Some((None, d))
        },
        Some(Some(v)) => {
            let d = ex_doc_x(v.as_slice(), tape, enc, load, ld, fuel);
            Some((Some(v), d))
        },
    }
}

} // verus!

impl Loader {
    /// A loader that reads with `f`: given the URI of the entity holding
    /// the declaration ("" for the document), the system identifier and
    /// the public identifier, it gives the entity's bytes and its URI
    /// (relative system identifiers in it are resolved against that), or
    /// `None` to leave the entity unread.
    pub fn new(f: impl FnMut(&[u8], &[u8], &[u8]) -> Option<(Vec<u8>, Vec<u8>)> + 'static) -> Self {
        Loader { f: Box::new(f), cache: Vec::new(), count: 0, bytes: 0, trace: Vec::new(), open: Vec::new(), fetching: Vec::new() }
    }

    /// A loader that reads nothing.
    pub fn none() -> Self {
        Loader::new(|_, _, _| None)
    }
}

thread_local! {
    static OPEN: std::cell::RefCell<Vec<Vec<u8>>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// While a loader's function runs: the names of the parameter entities
/// whose text is being read, outermost first, then the one it is asked
/// for ("" for the external subset).
#[cfg_attr(not(any(feature = "expat-abi", feature = "libxml2-abi")), allow(dead_code))]
pub(crate) fn open_entities() -> Vec<Vec<u8>> {
    OPEN.with(|o| o.borrow().clone())
}
