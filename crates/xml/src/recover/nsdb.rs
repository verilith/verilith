//! The namespace database (`xmlParserNsData`, parser.c 1453-1890).
//!
//! libxml2 keeps the bindings in scope in `nsTab` with a hash from prefix
//! to the latest binding and, per binding, the one it hides (`oldIndex`).
//! The latest binding of a prefix is the last one in `nsTab` with that
//! prefix (bindings are pushed and popped in stack order), which is what a
//! lookup here finds; the hash only makes that fast.
use super::*;
use crate::lenient::{bytes_eq, opt_eq, opt_to_vec, vec_of};
use vstd::prelude::*;

verus! {


pub const NONE: usize = usize::MAX;

pub struct NsEntry {
    pub prefix: Option<Vec<u8>>,
    pub uri: Vec<u8>,
    pub element_id: u32,
}

pub struct NsDb {
    pub tab: Vec<NsEntry>,
    pub element_id: u32,
    pub min: usize,
}

impl NsDb {
    pub fn new(_seed: u32) -> (r: NsDb)
        ensures
            r.tab@.len() == 0,
    {
        NsDb { tab: Vec::new(), element_id: 0, min: 0 }
    }

    /// `xmlParserNsLookup`: the index of the binding of `prefix` in effect,
    /// `NONE` if none (the minimum is not applied).
    pub fn lookup(&self, prefix: Option<&[u8]>) -> (r: usize)
        ensures
            r == NONE || r < self.tab@.len(),
    {
        let mut i = self.tab.len();
        while i > 0
            invariant
                i <= self.tab@.len(),
            decreases i,
        {
            i = i - 1;
            if opt_eq(opt_slice(&self.tab[i].prefix), prefix) {
                return i;
            }
        }
        NONE
    }

    /// `xmlParserNsStartElement`.
    pub fn start_element(&mut self) -> bool
        ensures
            final(self).tab == old(self).tab,
            final(self).min == old(self).min,
    {
        if self.element_id == u32::MAX {
            return false;
        }
        self.element_id = self.element_id + 1;
        true
    }
}

impl<S: Sink> Parser<S> {
    /// `xmlParserNsLookupUri`: the URI bound to `prefix` and visible, not "".
    pub fn ns_lookup_uri(&self, prefix: Option<&[u8]>) -> Option<Vec<u8>> {
        if opt_eq(prefix, Some(b"xml")) {
            return Some(vec_of(b"http://www.w3.org/XML/1998/namespace"));
        }
        let i = self.nsdb.lookup(prefix);
        if i == NONE || i < self.nsdb.min {
            return None;
        }
        let u = &self.nsdb.tab[i].uri;
        if u.len() == 0 {
            return None;
        }
        Some(u.clone())
    }

    /// `xmlParserNsPush`: 1 pushed, 0 not (a duplicate or redundant), -1.
    pub fn ns_push(&mut self, prefix: Option<&[u8]>, uri: &[u8], def_attr: bool) -> (r: i32)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).names == old(self).names,
            final(self).nsdb.min == old(self).nsdb.min,
            final(self).nsdb.tab@.len() == old(self).nsdb.tab@.len() + if r == 1 { 1int } else { 0int },
            0 <= r <= 1,
    {
        if opt_eq(prefix, Some(b"xml")) {
            return 0;
        }
        let old = self.nsdb.lookup(prefix);
        if old != NONE {
            if self.nsdb.tab[old].element_id == self.nsdb.element_id {
                if !def_attr {
                    match prefix {
                        None => self.err_attribute_dup(None, b"xmlns"),
                        Some(p) => self.err_attribute_dup(Some(b"xmlns"), p),
                    }
                }
                return 0;
            }
            if self.options & (1 << 13) != 0 && bytes_eq(self.nsdb.tab[old].uri.as_slice(), uri) {
                return 0;
            }
        }
        let e = NsEntry { prefix: opt_to_vec(prefix), uri: vec_of(uri), element_id: self.nsdb.element_id };
        self.nsdb.tab.push(e);
        self.sink.ns_pushed(prefix, uri);
        1
    }

    /// `xmlParserNsPop`.
    pub fn ns_pop(&mut self, nr: usize) -> (r: usize)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).names == old(self).names,
            final(self).nsdb.min == old(self).nsdb.min,
            r <= nr,
            final(self).nsdb.tab@.len() == old(self).nsdb.tab@.len() - r,
    {
        let n = if nr < self.nsdb.tab.len() { nr } else { self.nsdb.tab.len() };
        let keep = self.nsdb.tab.len() - n;
        self.nsdb.tab.truncate(keep);
        if n > 0 {
            self.sink.ns_popped(n);
        }
        n
    }

    pub fn set_ns_min(&mut self, min: usize)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).inputs == old(self).inputs,
            final(self).fuel == old(self).fuel,
            final(self).names == old(self).names,
            final(self).nsdb.tab == old(self).nsdb.tab,
    {
        self.nsdb.min = min;
        self.sink.ns_min(min);
    }
}

} // verus!
