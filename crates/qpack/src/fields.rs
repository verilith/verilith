//! Decoded field lines, stored in one buffer.
use crate::spec::*;
use verilith_core::prims::extend;
use vstd::prelude::*;

verus! {

/// A field line in `Fields::buf`: the name at `start`, `nlen` bytes, then
/// the value, `vlen` bytes.
#[derive(Clone, Copy)]
pub struct Line {
    pub start: usize,
    pub nlen: usize,
    pub vlen: usize,
    /// The N bit: the field must stay a literal on later hops.
    pub never: bool,
}

/// Field lines: their bytes, one after another, and where each is.
pub struct Fields {
    pub buf: Vec<u8>,
    pub lines: Vec<Line>,
}

impl Fields {
    pub open spec fn line_ok(&self, l: Line) -> bool {
        l.start + l.nlen + l.vlen <= self.buf@.len()
    }

    pub open spec fn field(&self, l: Line) -> Field {
        Field {
            name: self.buf@.subrange(l.start as int, l.start + l.nlen),
            value: self.buf@.subrange(l.start + l.nlen, l.start + l.nlen + l.vlen),
            never: l.never,
        }
    }

    pub open spec fn inv(&self) -> bool {
        forall|i: int| 0 <= i < self.lines@.len() ==> self.line_ok(#[trigger] self.lines@[i])
    }

    pub open spec fn view(&self) -> Seq<Field> {
        Seq::new(self.lines@.len(), |i: int| self.field(self.lines@[i]))
    }

    pub fn new() -> (r: Fields)
        ensures
            r.inv(),
            r.view() == Seq::<Field>::empty(),
    {
        let r = Fields { buf: Vec::new(), lines: Vec::new() };
        proof {
            assert(r.view() =~= Seq::<Field>::empty());
        }
        r
    }

    pub fn clear(&mut self)
        ensures
            final(self).inv(),
            final(self).view() == Seq::<Field>::empty(),
    {
        self.buf.clear();
        self.lines.clear();
        proof {
            assert(self.view() =~= Seq::<Field>::empty());
        }
    }

    /// The number of lines.
    pub fn len(&self) -> (r: usize)
        ensures
            r == self.view().len(),
    {
        self.lines.len()
    }

    /// Line `i`'s name and value.
    pub fn get(&self, i: usize) -> (r: (&[u8], &[u8], bool))
        requires
            self.inv(),
            i < self.view().len(),
        ensures
            r.0@ == self.view()[i as int].name,
            r.1@ == self.view()[i as int].value,
            r.2 == self.view()[i as int].never,
            r.0@.len() + r.1@.len() <= self.buf@.len(),
    {
        let l = self.lines[i];
        let _bl = self.buf.len();
        proof {
            assert(self.line_ok(self.lines@[i as int]));
        }
        let n = vstd::slice::slice_subrange(self.buf.as_slice(), l.start, l.start + l.nlen);
        let v = vstd::slice::slice_subrange(self.buf.as_slice(), l.start + l.nlen, l.start + l.nlen + l.vlen);
        (n, v, l.never)
    }

    /// Appends a field line.
    pub fn push(&mut self, name: &[u8], value: &[u8], never: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).view() == old(self).view().push(Field { name: name@, value: value@, never }),
    {
        let ghost b0 = self.buf@;
        let start = self.buf.len();
        extend(&mut self.buf, name);
        extend(&mut self.buf, value);
        let l = Line { start, nlen: name.len(), vlen: value.len(), never };
        let ghost l0 = self.lines@;
        self.lines.push(l);
        proof {
            assert(self.buf@ =~= b0 + name@ + value@);
            assert forall|i: int| 0 <= i < self.lines@.len() implies self.line_ok(#[trigger] self.lines@[i]) by {
                if i < l0.len() {
                    assert(self.lines@[i] == l0[i]);
                }
            }
            assert forall|i: int| 0 <= i < l0.len() implies #[trigger] self.field(self.lines@[i]) == old(self).field(l0[i]) by {
                let li = l0[i];
                assert(old(self).line_ok(li));
                assert(self.buf@.subrange(li.start as int, li.start + li.nlen) =~= b0.subrange(li.start as int, li.start + li.nlen));
                assert(self.buf@.subrange(li.start + li.nlen, li.start + li.nlen + li.vlen) =~= b0.subrange(li.start + li.nlen, li.start + li.nlen + li.vlen));
            }
            assert(self.field(l).name =~= name@);
            assert(self.field(l).value =~= value@);
            assert(self.view() =~= old(self).view().push(Field { name: name@, value: value@, never }));
        }
    }
}

} // verus!
