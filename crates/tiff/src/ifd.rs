//! The header and IFD fields (§2), proven against `spec::header`,
//! `spec::find`, `spec::field` and `spec::scalar`.
use crate::spec::*;
use verilith_core::prims::get;
use vstd::prelude::*;

verus! {

#[inline(always)]
pub fn u16_exec(b: &[u8], le: bool, i: usize) -> (r: u16)
    requires
        i + 1 < b@.len(),
    ensures
        r as nat == u16_at(b@, le, i as int),
{
    let l = b.len();
    let x = get(b, i) as u16;
    let y = get(b, i + 1) as u16;
    if le {
        x + 256 * y
    } else {
        256 * x + y
    }
}

#[inline(always)]
pub fn u32_exec(b: &[u8], le: bool, i: usize) -> (r: u32)
    requires
        i + 3 < b@.len(),
    ensures
        r as nat == u32_at(b@, le, i as int),
{
    let l = b.len();
    let x = u16_exec(b, le, i) as u32;
    let y = u16_exec(b, le, i + 2) as u32;
    if le {
        x + 65536 * y
    } else {
        65536 * x + y
    }
}

/// The byte order and the offset of IFD 0 (`spec::header`).
pub fn header_exec(b: &[u8]) -> (r: Option<(bool, u32)>)
    ensures
        match header(b@) {
            Some((le, o)) => r == Some((le, o as u32)),
            None => r is None,
        },
{
    if b.len() < 8 {
        return None;
    }
    let a = get(b, 0);
    let c = get(b, 1);
    if !((a == 0x49 && c == 0x49) || (a == 0x4D && c == 0x4D)) {
        return None;
    }
    let le = a == 0x49;
    if u16_exec(b, le, 2) != 42 {
        return None;
    }
    let o = u32_exec(b, le, 4);
    if o % 2 != 0 || o < 8 {
        return None;
    }
    Some((le, o))
}

/// `spec::bigtiff`.
pub fn bigtiff_exec(b: &[u8]) -> (r: bool)
    ensures
        r == bigtiff(b@),
{
    b.len() >= 4 && ((get(b, 0) == 0x49 && get(b, 1) == 0x49 && get(b, 2) == 43 && get(b, 3) == 0)
        || (get(b, 0) == 0x4D && get(b, 1) == 0x4D && get(b, 2) == 0 && get(b, 3) == 43))
}

/// Whether the IFD's entries are in ascending order of tag
/// (`spec::sorted`).
pub fn sorted_exec(b: &[u8], le: bool, o: usize, n: usize) -> (r: bool)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        r == sorted(b@, le, o as nat, n as nat),
{
    let l = b.len();
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            l == b@.len(),
            ifd_ok(b@, o as nat, n as nat),
            i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] tag_at(b@, le, o as nat, j) < tag_at(b@, le, o as nat, j + 1),
        decreases n - i,
    {
        let e = o + 2 + 12 * i;
        if u16_exec(b, le, e) >= u16_exec(b, le, e + 12) {
            assert(!(tag_at(b@, le, o as nat, i as int) < tag_at(b@, le, o as nat, i + 1)));
            return false;
        }
        i = i + 1;
    }
    true
}

/// `spec::present`.
pub fn present_exec(b: &[u8], le: bool, o: usize, n: usize, tag: u16) -> (r: bool)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        r == present(b@, le, o as nat, n as nat, tag as nat),
{
    let l = b.len();
    match find_exec(b, le, o, n, tag) {
        None => false,
        Some(i) => {
            let ty = u16_exec(b, le, o + 2 + 12 * i + 2);
            ty == 1 || ty == 3 || ty == 4
        },
    }
}

/// An IFD inside the file: `n` entries at `o`.
pub open spec fn ifd_ok(b: Seq<u8>, o: nat, n: nat) -> bool {
    o + 2 + 12 * n <= b.len()
}

pub proof fn lemma_find_range(b: Seq<u8>, le: bool, o: nat, n: nat, tag: nat, i: nat)
    ensures
        find(b, le, o, n, tag, i) matches Some(j) ==> i <= j < n,
    decreases n - i,
{
    if i < n {
        lemma_find_range(b, le, o, n, tag, i + 1);
    }
}

/// The first entry with tag `tag` (`spec::find`).
pub fn find_exec(b: &[u8], le: bool, o: usize, n: usize, tag: u16) -> (r: Option<usize>)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        match find(b@, le, o as nat, n as nat, tag as nat, 0) {
            Some(i) => r == Some(i as usize) && i < n,
            None => r is None,
        },
{
    proof {
        lemma_find_range(b@, le, o as nat, n as nat, tag as nat, 0);
    }
    let l = b.len();
    let mut i: usize = 0;
    while i < n
        invariant
            l == b@.len(),
            ifd_ok(b@, o as nat, n as nat),
            i <= n,
            find(b@, le, o as nat, n as nat, tag as nat, 0) == find(b@, le, o as nat, n as nat, tag as nat, i as nat),
        decreases n - i,
    {
        let e = o + 2 + 12 * i;
        if u16_exec(b, le, e) == tag {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

/// A field whose values are inside the file.
#[derive(Clone, Copy)]
pub struct Field {
    pub ty: u16,
    pub count: u32,
    pub pos: usize,
}

impl Field {
    pub open spec fn ok(self, b: Seq<u8>) -> bool {
        &&& (self.ty == 1 || self.ty == 3 || self.ty == 4)
        &&& self.pos + self.count * type_size(self.ty as nat) <= b.len()
    }

    pub open spec fn values(self, b: Seq<u8>, le: bool) -> Seq<nat> {
        Seq::new(self.count as nat, |k: int| value(b, le, self.ty as nat, self.pos as int, k))
    }
}

/// The field with tag `tag` (`spec::field`): `Err` if the spec rejects it,
/// `Ok(None)` if there is none.
pub fn field_exec(b: &[u8], le: bool, o: usize, n: usize, tag: u16) -> (r: Result<Option<Field>, ()>)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        match field(b@, le, o as nat, n as nat, tag as nat) {
            None => r is Err,
            Some(None) => r == Ok::<Option<Field>, ()>(None),
            Some(Some(v)) => r matches Ok(Some(f)) && f.ok(b@) && f.values(b@, le) == v,
        },
{
    proof {
        reveal(field);
    }
    let l = b.len();
    let i = match find_exec(b, le, o, n, tag) {
        None => return Ok(None),
        Some(i) => i,
    };
    let e = o + 2 + 12 * i;
    let ty = u16_exec(b, le, e + 2);
    let cnt = u32_exec(b, le, e + 4);
    if ty != 1 && ty != 3 && ty != 4 {
        return Ok(None);
    }
    let ts: u64 = if ty == 1 { 1 } else if ty == 3 { 2 } else { 4 };
    let size = cnt as u64 * ts;
    let pos: u64 = if size <= 4 { e as u64 + 8 } else { u32_exec(b, le, e + 8) as u64 };
    if pos + size > b.len() as u64 {
        return Err(());
    }
    let f = Field { ty, count: cnt, pos: pos as usize };
    proof {
        assert(f.values(b@, le) =~= field(b@, le, o as nat, n as nat, tag as nat)->Some_0->Some_0);
    }
    Ok(Some(f))
}

/// Value `k` of a field (`spec::value`).
pub fn value_exec(b: &[u8], le: bool, f: Field, k: u32) -> (r: u32)
    requires
        f.ok(b@),
        k < f.count,
    ensures
        r as nat == value(b@, le, f.ty as nat, f.pos as int, k as int),
{
    proof {
        vstd::arithmetic::mul::lemma_mul_inequality(k as int + 1, f.count as int, type_size(f.ty as nat) as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(type_size(f.ty as nat) as int, k as int, 1);
    }
    let l = b.len();
    if f.ty == 1 {
        get(b, f.pos + k as usize) as u32
    } else if f.ty == 3 {
        u16_exec(b, le, f.pos + 2 * k as usize) as u32
    } else {
        u32_exec(b, le, f.pos + 4 * k as usize)
    }
}

/// A field with one value, or `default` (`spec::scalar`).
pub fn scalar_exec(b: &[u8], le: bool, o: usize, n: usize, tag: u16, default: u32) -> (r: Option<u32>)
    requires
        ifd_ok(b@, o as nat, n as nat),
    ensures
        match scalar(b@, le, o as nat, n as nat, tag as nat, default as nat) {
            Some(x) => r == Some(x as u32) && x <= u32::MAX,
            None => r is None,
        },
{
    proof {
        reveal(scalar);
    }
    match field_exec(b, le, o, n, tag) {
        Err(()) => None,
        Ok(None) => Some(default),
        Ok(Some(f)) => if f.count == 1 {
            Some(value_exec(b, le, f, 0))
        } else {
            None
        },
    }
}

} // verus!
