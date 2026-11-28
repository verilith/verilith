//! The guest ABI: the host functions a function module imports, their
//! specification ([`step`]), and the verified host that implements them
//! ([`Abi::dispatch`]).
//!
//! A guest reaches the request and builds its response only through these
//! five imports (module `vl`), each taking and returning `i32`s:
//!
//! | import | does |
//! |---|---|
//! | `req_size(part) -> len` | length of request part `part` (0 method, 1 target, 2 header lines, 3 body), or -1 |
//! | `req_read(part, off, dst, len) -> n` | copies `n = min(len, size - off)` bytes of the part from `off` to guest memory at `dst`, or -1 |
//! | `resp_status(code) -> 0` | sets the status (200 to 599), or -1 |
//! | `resp_header(name, name_len, value, value_len) -> 0` | adds a response field, or -1 |
//! | `resp_write(ptr, len) -> 0` | appends to the response body, or -1 |
//!
//! The theorem is [`Abi::dispatch`]'s contract: every host call does exactly
//! what [`step`] says, so the host writes guest memory only at
//! `dst..dst + n` of a `req_read` that fits, and only with request bytes;
//! it reads guest memory only inside it; and the reply it builds always
//! satisfies [`reply_ok`] (the [`Reply`] type invariant): a status from 200
//! to 599, at most the configured number and bytes of fields, each one a
//! field the server's verified serializer accepts (no CR, LF or NUL, so no
//! response splitting; no framing or hop-by-hop field), and at most the
//! configured body size.
use vstd::prelude::*;
use verilith_server::respond::{check_name, check_value, SField};
#[cfg(verus_only)]
use verilith_server::respond::{name_ok, value_ok};
#[cfg(verus_only)]
use verilith_http::spec as hs;
use verilith_wasm::interp::Host;
use verilith_wasm::mem::Mem;

verus! {

pub const OP_REQ_SIZE: u8 = 0;
pub const OP_REQ_READ: u8 = 1;
pub const OP_STATUS: u8 = 2;
pub const OP_HEADER: u8 = 3;
pub const OP_WRITE: u8 = 4;

/// -1 as an `i32` result slot.
pub const NEG1: u64 = 0xFFFF_FFFF;

/// Number of `i32` parameters of each import.
pub open spec fn arity(op: u8) -> nat {
    if op == OP_REQ_SIZE || op == OP_STATUS {
        1
    } else if op == OP_WRITE {
        2
    } else {
        4
    }
}

/// The name each ABI function is imported under, from module `vl`.
pub open spec fn op_name(op: u8) -> Seq<u8> {
    if op == OP_REQ_SIZE {
        seq![0x72u8, 0x65, 0x71, 0x5f, 0x73, 0x69, 0x7a, 0x65]  // req_size
    } else if op == OP_REQ_READ {
        seq![0x72u8, 0x65, 0x71, 0x5f, 0x72, 0x65, 0x61, 0x64]  // req_read
    } else if op == OP_STATUS {
        seq![0x72u8, 0x65, 0x73, 0x70, 0x5f, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73]  // resp_status
    } else if op == OP_HEADER {
        seq![0x72u8, 0x65, 0x73, 0x70, 0x5f, 0x68, 0x65, 0x61, 0x64, 0x65, 0x72]  // resp_header
    } else {
        seq![0x72u8, 0x65, 0x73, 0x70, 0x5f, 0x77, 0x72, 0x69, 0x74, 0x65]  // resp_write
    }
}

fn op_name_vec(op: u8) -> (r: Vec<u8>)
    ensures r@ == op_name(op),
{
    let r = if op == OP_REQ_SIZE {
        vec![0x72u8, 0x65, 0x71, 0x5f, 0x73, 0x69, 0x7a, 0x65]
    } else if op == OP_REQ_READ {
        vec![0x72u8, 0x65, 0x71, 0x5f, 0x72, 0x65, 0x61, 0x64]
    } else if op == OP_STATUS {
        vec![0x72u8, 0x65, 0x73, 0x70, 0x5f, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73]
    } else if op == OP_HEADER {
        vec![0x72u8, 0x65, 0x73, 0x70, 0x5f, 0x68, 0x65, 0x61, 0x64, 0x65, 0x72]
    } else {
        vec![0x72u8, 0x65, 0x73, 0x70, 0x5f, 0x77, 0x72, 0x69, 0x74, 0x65]
    };
    proof { assert(r@ =~= op_name(op)); }
    r
}

fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            0 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof { assert(a@ =~= b@); }
    true
}

/// The ABI function imported under `name` (from module `vl`), if any.
/// The loader builds the import table from this, so import `i` is the
/// ABI function its name says.
pub fn op_of(name: &[u8]) -> (r: Option<u8>)
    ensures
        r matches Some(op) ==> op <= OP_WRITE && name@ == op_name(op),
        r is None ==> forall|op: u8| op <= OP_WRITE ==> name@ != op_name(op),
{
    let mut op: u8 = 0;
    while op <= OP_WRITE
        invariant
            op <= OP_WRITE + 1,
            forall|o: u8| o < op ==> name@ != op_name(o),
        decreases OP_WRITE + 1 - op,
    {
        let n = op_name_vec(op);
        if bytes_eq(name, n.as_slice()) {
            return Some(op);
        }
        op += 1;
    }
    None
}

/// The number of `i32` parameters of ABI function `op` ([`arity`]).
pub fn arity_of(op: u8) -> (r: usize)
    ensures r == arity(op),
{
    if op == OP_REQ_SIZE || op == OP_STATUS { 1 } else if op == OP_WRITE { 2 } else { 4 }
}

/// An `i32` argument as the unsigned number the guest meant (pointers and
/// lengths are `u32` in wasm32).
pub open spec fn lo(x: u64) -> nat {
    (x % 0x1_0000_0000) as nat
}

// ---------------------------------------------------------------------------
// Response fields a guest may set
// ---------------------------------------------------------------------------

pub open spec fn lit_connection() -> Seq<u8> {
    seq![0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e]
}

pub open spec fn lit_keep_alive() -> Seq<u8> {
    seq![0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65]
}

pub open spec fn lit_proxy_connection() -> Seq<u8> {
    seq![0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e]
}

pub open spec fn lit_upgrade() -> Seq<u8> {
    seq![0x75u8, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65]
}

pub open spec fn lit_te() -> Seq<u8> {
    seq![0x74u8, 0x65]
}

pub open spec fn lit_trailer() -> Seq<u8> {
    seq![0x74u8, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72]
}

/// Connection-specific fields (RFC 9110 §7.6.1, RFC 9113 §8.2.2), which
/// the server decides and a guest may not send.
pub open spec fn hop(n: Seq<u8>) -> bool {
    ||| hs::ci_eq_dash(n, lit_connection())
    ||| hs::ci_eq_dash(n, lit_keep_alive())
    ||| hs::ci_eq_dash(n, lit_proxy_connection())
    ||| hs::ci_eq_dash(n, lit_upgrade())
    ||| hs::ci_eq_dash(n, lit_te())
    ||| hs::ci_eq_dash(n, lit_trailer())
}

/// A field a guest may send: what the server's serializer accepts
/// (`respond::name_ok`: a token, not Content-Length or Transfer-Encoding;
/// `respond::value_ok`: no CR, LF, NUL or DEL), and not hop-by-hop.
pub open spec fn field_ok(n: Seq<u8>, v: Seq<u8>) -> bool {
    name_ok(n) && value_ok(v) && !hop(n)
}

#[inline]
fn lower(c: u8) -> (r: u8)
    ensures r == hs::lower(c),
{
    if c >= 0x41 && c <= 0x5A { c + 0x20 } else { c }
}

fn eq_dash(n: &[u8], lit: &[u8]) -> (r: bool)
    ensures r == hs::ci_eq_dash(n@, lit@),
{
    if n.len() != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < n.len()
        invariant
            n.len() == lit.len(),
            0 <= i <= n.len(),
            forall|j: int| 0 <= j < i ==> hs::lower(#[trigger] n@[j]) == lit@[j]
                || (n@[j] == 0x5F && lit@[j] == 0x2D),
        decreases n.len() - i,
    {
        let c = n[i];
        if !(lower(c) == lit[i] || (c == 0x5F && lit[i] == 0x2D)) {
            return false;
        }
        i += 1;
    }
    true
}

/// Whether `n` is a hop-by-hop field name ([`hop`]).
pub fn check_hop(n: &[u8]) -> (r: bool)
    ensures r == hop(n@),
{
    let a: [u8; 10] = [0x63u8, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
    let b: [u8; 10] = [0x6bu8, 0x65, 0x65, 0x70, 0x2d, 0x61, 0x6c, 0x69, 0x76, 0x65];
    let c: [u8; 16] = [0x70u8, 0x72, 0x6f, 0x78, 0x79, 0x2d, 0x63, 0x6f, 0x6e, 0x6e, 0x65, 0x63, 0x74, 0x69, 0x6f, 0x6e];
    let d: [u8; 7] = [0x75u8, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65];
    let e: [u8; 2] = [0x74u8, 0x65];
    let f: [u8; 7] = [0x74u8, 0x72, 0x61, 0x69, 0x6c, 0x65, 0x72];
    assert(a@ =~= lit_connection());
    assert(b@ =~= lit_keep_alive());
    assert(c@ =~= lit_proxy_connection());
    assert(d@ =~= lit_upgrade());
    assert(e@ =~= lit_te());
    assert(f@ =~= lit_trailer());
    eq_dash(n, &a) || eq_dash(n, &b) || eq_dash(n, &c) || eq_dash(n, &d) || eq_dash(n, &e)
        || eq_dash(n, &f)
}

/// Whether a guest may send this field ([`field_ok`]).
pub fn check_field(n: &[u8], v: &[u8]) -> (r: bool)
    ensures r == field_ok(n@, v@),
{
    check_name(n) && check_value(v) && !check_hop(n)
}

// ---------------------------------------------------------------------------
// The request, the limits and the reply
// ---------------------------------------------------------------------------

/// What a reply may hold.
#[derive(Clone, Copy)]
pub struct Limits {
    /// Most body bytes.
    pub max_body: usize,
    /// Most fields.
    pub max_fields: usize,
    /// Most bytes of field names and values together.
    pub max_field_bytes: usize,
}

/// The request, as the guest reads it: four byte strings.
#[derive(Clone, Copy)]
pub struct Req<'a> {
    pub method: &'a [u8],
    pub target: &'a [u8],
    /// The header lines, `name: value\r\n` each, as the server parsed them.
    pub fields: &'a [u8],
    pub body: &'a [u8],
}

impl<'a> Req<'a> {
    /// Part `k`, or empty past the last.
    pub open spec fn part(&self, k: nat) -> Seq<u8> {
        if k == 0 {
            self.method@
        } else if k == 1 {
            self.target@
        } else if k == 2 {
            self.fields@
        } else if k == 3 {
            self.body@
        } else {
            Seq::empty()
        }
    }

    fn get(&self, k: u32) -> (r: &'a [u8])
        requires k < 4,
        ensures r@ == self.part(k as nat),
    {
        if k == 0 {
            self.method
        } else if k == 1 {
            self.target
        } else if k == 2 {
            self.fields
        } else {
            self.body
        }
    }
}

/// A response field the guest set (copied out of its memory).
pub struct OutField {
    pub name: Vec<u8>,
    pub value: Vec<u8>,
}

/// The reply, as the spec sees it.
pub ghost struct RView {
    pub status: u16,
    pub fields: Seq<SField>,
    pub field_bytes: nat,
    pub body: Seq<u8>,
}

/// What every reply satisfies, whatever the guest did.
pub open spec fn reply_ok(lim: Limits, r: RView) -> bool {
    &&& 200 <= r.status <= 599
    &&& r.fields.len() <= lim.max_fields
    &&& r.field_bytes <= lim.max_field_bytes
    &&& r.body.len() <= lim.max_body
    &&& forall|i: int| 0 <= i < r.fields.len() ==> field_ok(#[trigger] r.fields[i].0, r.fields[i].1)
}

/// The reply a request starts with: 200, no fields, empty body.
pub open spec fn reply0() -> RView {
    RView { status: 200, fields: Seq::empty(), field_bytes: 0, body: Seq::empty() }
}

/// The reply being built. Its fields are private, so the type invariant
/// ([`reply_ok`]) holds for every `Reply` there is.
pub struct Reply {
    lim: Limits,
    status: u16,
    fields: Vec<OutField>,
    field_bytes: usize,
    body: Vec<u8>,
}

pub open spec fn out_view(f: OutField) -> SField {
    (f.name@, f.value@)
}

impl Reply {
    pub closed spec fn view(&self) -> RView {
        RView {
            status: self.status,
            fields: self.fields@.map_values(|f: OutField| out_view(f)),
            field_bytes: self.field_bytes as nat,
            body: self.body@,
        }
    }

    pub closed spec fn limits(&self) -> Limits {
        self.lim
    }

    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        reply_ok(self.lim, self.view())
    }

    /// An empty reply ([`reply0`]).
    pub fn new(lim: Limits) -> (r: Reply)
        ensures r.view() == reply0(), r.limits() == lim,
    {
        let r = Reply { lim, status: 200, fields: Vec::new(), field_bytes: 0, body: Vec::new() };
        assert(r.view().fields =~= Seq::<SField>::empty());
        r
    }

    /// Every reply satisfies [`reply_ok`] (the type invariant).
    #[inline(always)]
    pub fn lemma_ok(&self)
        ensures reply_ok(self.limits(), self.view()),
    {
        proof { use_type_invariant(self); }
    }

    pub fn lim(&self) -> (r: Limits)
        ensures r == self.limits(),
    {
        self.lim
    }

    pub fn status(&self) -> (r: u16)
        ensures r == self.view().status,
    {
        self.status
    }

    pub fn body(&self) -> (r: &[u8])
        ensures r@ == self.view().body,
    {
        self.body.as_slice()
    }

    pub fn n_fields(&self) -> (r: usize)
        ensures r == self.view().fields.len(),
    {
        self.fields.len()
    }

    /// Field `i`, as (name, value).
    pub fn field(&self, i: usize) -> (r: (&[u8], &[u8]))
        requires i < self.view().fields.len(),
        ensures
            r.0@ == self.view().fields[i as int].0,
            r.1@ == self.view().fields[i as int].1,
    {
        let f = &self.fields[i];
        (f.name.as_slice(), f.value.as_slice())
    }
}

// ---------------------------------------------------------------------------
// The specification of the host calls
// ---------------------------------------------------------------------------

/// `mem` with `src` written at `dst`.
pub open spec fn put(mem: Seq<u8>, dst: nat, src: Seq<u8>) -> Seq<u8> {
    mem.subrange(0, dst as int) + src + mem.subrange((dst + src.len()) as int, mem.len() as int)
}

/// One host call with well-formed arity: the new reply, the `i32` result
/// (as a slot) and the new guest memory.
pub open spec fn step(q: Req, lim: Limits, r: RView, op: u8, a: Seq<u64>, mem: Seq<u8>) -> (RView, u64, Seq<u8>) {
    if op == OP_REQ_SIZE {
        let k = lo(a[0]);
        if k < 4 && q.part(k).len() < 0x8000_0000 {
            (r, q.part(k).len() as u64, mem)
        } else {
            (r, NEG1, mem)
        }
    } else if op == OP_REQ_READ {
        let (k, off, dst, n) = (lo(a[0]), lo(a[1]), lo(a[2]), lo(a[3]));
        let p = q.part(k);
        if k < 4 && off <= p.len() && dst + n <= mem.len() {
            let c = if n <= p.len() - off { n } else { (p.len() - off) as nat };
            (r, c as u64, put(mem, dst, p.subrange(off as int, (off + c) as int)))
        } else {
            (r, NEG1, mem)
        }
    } else if op == OP_STATUS {
        let s = lo(a[0]);
        if 200 <= s <= 599 {
            (RView { status: s as u16, ..r }, 0, mem)
        } else {
            (r, NEG1, mem)
        }
    } else if op == OP_HEADER {
        let (np, nl, vp, vl) = (lo(a[0]), lo(a[1]), lo(a[2]), lo(a[3]));
        if np + nl <= mem.len() && vp + vl <= mem.len() {
            let n = mem.subrange(np as int, (np + nl) as int);
            let v = mem.subrange(vp as int, (vp + vl) as int);
            if field_ok(n, v) && r.fields.len() < lim.max_fields
                && r.field_bytes + nl + vl <= lim.max_field_bytes {
                (RView { fields: r.fields.push((n, v)), field_bytes: (r.field_bytes + nl + vl) as nat, ..r }, 0, mem)
            } else {
                (r, NEG1, mem)
            }
        } else {
            (r, NEG1, mem)
        }
    } else {
        let (p, n) = (lo(a[0]), lo(a[1]));
        if p + n <= mem.len() && r.body.len() + n <= lim.max_body {
            (RView { body: r.body + mem.subrange(p as int, (p + n) as int), ..r }, 0, mem)
        } else {
            (r, NEG1, mem)
        }
    }
}

/// Whether a call of import `func` is well-formed: a known import, called
/// with its number of arguments and one result. Anything else traps.
pub open spec fn call_ok(ops: Seq<u8>, func: nat, nargs: nat, nres: nat) -> bool {
    &&& func < ops.len()
    &&& ops[func as int] <= OP_WRITE
    &&& nargs == arity(ops[func as int])
    &&& nres == 1
}

/// The step preserves [`reply_ok`].
pub proof fn lemma_step_ok(q: Req, lim: Limits, r: RView, op: u8, a: Seq<u64>, mem: Seq<u8>)
    requires reply_ok(lim, r), a.len() == arity(op),
    ensures reply_ok(lim, step(q, lim, r, op, a, mem).0),
{
    let r2 = step(q, lim, r, op, a, mem).0;
    if op == OP_HEADER && r2.fields.len() == r.fields.len() + 1 {
        assert forall|i: int| 0 <= i < r2.fields.len() implies field_ok(#[trigger] r2.fields[i].0, r2.fields[i].1) by {
            if i < r.fields.len() {
                assert(r2.fields[i] == r.fields[i]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The verified host
// ---------------------------------------------------------------------------

/// The low 32 bits of a slot: the `i32` argument as a `u32`.
#[inline(always)]
fn low(x: u64) -> (r: u32)
    ensures r as nat == lo(x),
{
    let y = x & 0xFFFF_FFFF;
    assert(y == x % 0x1_0000_0000 && y <= 0xFFFF_FFFF) by (bit_vector)
        requires y == x & 0xFFFF_FFFF;
    y as u32
}

#[inline(always)]
fn slice_range(b: &[u8], i: usize, n: usize) -> (r: &[u8])
    requires i + n <= b@.len(),
    ensures r@ == b@.subrange(i as int, i + n),
{
    let _ = b.len();
    // SAFETY: in bounds by the precondition.
    unsafe { b.get_unchecked(i..i + n) }
}

#[inline(always)]
fn set_result(r: &mut [u64], v: u64)
    requires old(r)@.len() == 1,
    ensures final(r)@ == seq![v],
{
    // SAFETY: in bounds by the precondition.
    unsafe { *r.get_unchecked_mut(0) = v }
    assert(final(r)@ =~= seq![v]);
}

/// The host for one request: the request, which import is which ABI
/// function, and the reply being built.
pub struct Abi<'a> {
    pub req: Req<'a>,
    /// `ops[i]` is the ABI function behind import `i` (from [`crate::host`]).
    pub ops: &'a [u8],
    pub reply: Reply,
}

impl<'a> Abi<'a> {
    /// Runs one host call. A malformed call (unknown import, wrong arity)
    /// traps and changes nothing; a well-formed one does exactly [`step`].
    pub fn dispatch(&mut self, func: u32, args: &[u64], results: &mut [u64], mem: &mut Mem) -> (ok: bool)
        ensures
            final(self).req == old(self).req,
            final(self).ops == old(self).ops,
            final(self).reply.limits() == old(self).reply.limits(),
            ok == call_ok(old(self).ops@, func as nat, args@.len(), old(results)@.len()),
            ok ==> ({
                let (r2, v, m2) = step(old(self).req, old(self).reply.limits(), old(self).reply.view(),
                    old(self).ops@[func as int], args@, old(mem)@);
                &&& final(self).reply.view() == r2
                &&& final(results)@ == seq![v]
                &&& final(mem)@ == m2
            }),
            !ok ==> final(self).reply.view() == old(self).reply.view() && final(mem)@ == old(mem)@
                && final(results)@ == old(results)@,
    {
        let f = func as usize;
        if f >= self.ops.len() || results.len() != 1 {
            return false;
        }
        let op = self.ops[f];
        if op > OP_WRITE {
            return false;
        }
        let want: usize = if op == OP_REQ_SIZE || op == OP_STATUS { 1 } else if op == OP_WRITE { 2 } else { 4 };
        if args.len() != want {
            return false;
        }
        let ghost r0 = self.reply.view();
        let ghost m0 = mem@;
        proof { use_type_invariant(&self.reply); }
        if op == OP_REQ_SIZE {
            let k = low(args[0]);
            assert(k as nat == lo(args@[0]));
            if k < 4 {
                let n = self.req.get(k).len();
                if n < 0x8000_0000 {
                    set_result(results, n as u64);
                    return true;
                }
            }
            set_result(results, NEG1);
            true
        } else if op == OP_REQ_READ {
            let k = low(args[0]);
            let off = low(args[1]) as usize;
            let dst = low(args[2]) as usize;
            let n = low(args[3]) as usize;
            assert(k as nat == lo(args@[0]) && off as nat == lo(args@[1]) && dst as nat == lo(args@[2])
                && n as nat == lo(args@[3]));
            if k < 4 {
                let p = self.req.get(k);
                if off <= p.len() && dst <= mem.len() && n <= mem.len() - dst {
                    let c = if n <= p.len() - off { n } else { p.len() - off };
                    let _ = mem.write(dst, p, off, c);
                    proof {
                        assert(final(mem)@ =~= put(m0, dst as nat, p@.subrange(off as int, off + c)));
                    }
                    set_result(results, c as u64);
                    return true;
                }
            }
            set_result(results, NEG1);
            true
        } else if op == OP_STATUS {
            let s = low(args[0]);
            assert(s as nat == lo(args@[0]));
            if s >= 200 && s <= 599 {
                self.reply.status = s as u16;
                proof {
                    assert(self.reply.view() =~= (RView { status: s as u16, ..r0 }));
                }
                set_result(results, 0);
            } else {
                set_result(results, NEG1);
            }
            true
        } else if op == OP_HEADER {
            let np = low(args[0]) as usize;
            let nl = low(args[1]) as usize;
            let vp = low(args[2]) as usize;
            let vl = low(args[3]) as usize;
            assert(np as nat == lo(args@[0]) && nl as nat == lo(args@[1]) && vp as nat == lo(args@[2])
                && vl as nat == lo(args@[3]));
            if np <= mem.len() && nl <= mem.len() - np && vp <= mem.len() && vl <= mem.len() - vp {
                let n = slice_range(mem.as_slice(), np, nl);
                let v = slice_range(mem.as_slice(), vp, vl);
                let lim = self.reply.lim;
                if check_field(n, v) && self.reply.fields.len() < lim.max_fields
                    && self.reply.field_bytes <= lim.max_field_bytes
                    && nl <= lim.max_field_bytes - self.reply.field_bytes
                    && vl <= lim.max_field_bytes - self.reply.field_bytes - nl {
                    let mut name: Vec<u8> = Vec::new();
                    name.extend_from_slice(n);
                    let mut value: Vec<u8> = Vec::new();
                    value.extend_from_slice(v);
                    proof {
                        assert(name@ =~= n@);
                        assert(value@ =~= v@);
                    }
                    let mut old_reply = Reply::new(lim);
                    core::mem::swap(&mut self.reply, &mut old_reply);
                    let Reply { lim: l2, status, mut fields, field_bytes, body } = old_reply;
                    fields.push(OutField { name, value });
                    proof {
                        assert(fields@.map_values(|f: OutField| out_view(f)) =~= r0.fields.push((n@, v@)));
                        lemma_step_ok(self.req, lim, r0, op, args@, m0);
                    }
                    self.reply = Reply { lim: l2, status, fields, field_bytes: field_bytes + nl + vl, body };
                    proof {
                        assert(self.reply.view().fields =~= r0.fields.push((n@, v@)));
                        assert(self.reply.view() =~= (RView {
                            fields: r0.fields.push((n@, v@)), field_bytes: (r0.field_bytes + nl + vl) as nat, ..r0 }));
                        lemma_step_ok(self.req, lim, r0, op, args@, m0);
                    }
                    set_result(results, 0);
                    return true;
                }
            }
            set_result(results, NEG1);
            true
        } else {
            let p = low(args[0]) as usize;
            let n = low(args[1]) as usize;
            assert(p as nat == lo(args@[0]) && n as nat == lo(args@[1]));
            let lim = self.reply.lim;
            if p <= mem.len() && n <= mem.len() - p && n <= lim.max_body - self.reply.body.len() {
                let s = slice_range(mem.as_slice(), p, n);
                let mut old_reply = Reply::new(lim);
                core::mem::swap(&mut self.reply, &mut old_reply);
                let Reply { lim: l2, status, fields, field_bytes, mut body } = old_reply;
                body.extend_from_slice(s);
                proof { assert(body@ =~= r0.body + m0.subrange(p as int, p + n)); }
                self.reply = Reply { lim: l2, status, fields, field_bytes, body };
                proof {
                    assert(self.reply.body@ =~= r0.body + m0.subrange(p as int, p + n));
                    assert(self.reply.view() =~= (RView { body: r0.body + m0.subrange(p as int, p + n), ..r0 }));
                }
                set_result(results, 0);
            } else {
                set_result(results, NEG1);
            }
            true
        }
    }
}

impl<'a> Host for Abi<'a> {
    fn call(&mut self, func: u32, args: &[u64], results: &mut [u64], mem: &mut Mem) -> bool {
        self.dispatch(func, args, results, mem)
    }
}

} // verus!
