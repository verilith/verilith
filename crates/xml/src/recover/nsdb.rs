//! The namespace database (`xmlParserNsData`, parser.c 1453-1890).
//!
//! libxml2 keeps the bindings in scope in `nsTab` with a hash from prefix
//! to the latest binding and, per binding, the one it hides (`oldIndex`).
//! The latest binding of a prefix is the last one in `nsTab` with that
//! prefix (bindings are pushed and popped in stack order), which is what a
//! lookup here finds; the hash only makes that fast.
use super::*;
use vstd::prelude::*;

verus! {


pub const NONE: usize = usize::MAX;

#[derive(Clone)]
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
    #[verifier::external_body]
    pub fn new(_seed: u32) -> NsDb {
        NsDb { tab: Vec::new(), element_id: 0, min: 0 }
    }

    /// `xmlParserNsLookup`: the index of the binding of `prefix` in effect,
    /// `NONE` if none (the minimum is not applied).
    #[verifier::external_body]
    pub fn lookup(&self, prefix: Option<&[u8]>) -> usize {
        let mut i = self.tab.len();
        while i > 0 {
            i -= 1;
            if self.tab[i].prefix.as_deref() == prefix {
                return i;
            }
        }
        NONE
    }

    /// `xmlParserNsStartElement`.
    #[verifier::external_body]
    pub fn start_element(&mut self) -> bool {
        if self.element_id == u32::MAX {
            return false;
        }
        self.element_id += 1;
        true
    }
}

impl<S: Sink> Parser<S> {
    /// `xmlParserNsLookupUri`: the URI bound to `prefix` and visible, not "".
    #[verifier::external_body]
    pub fn ns_lookup_uri(&self, prefix: Option<&[u8]>) -> Option<Vec<u8>> {
        if prefix == Some(b"xml") {
            return Some(b"http://www.w3.org/XML/1998/namespace".to_vec());
        }
        let i = self.nsdb.lookup(prefix);
        if i == NONE || i < self.nsdb.min {
            return None;
        }
        let u = &self.nsdb.tab[i].uri;
        if u.is_empty() {
            return None;
        }
        Some(u.clone())
    }

    /// `xmlParserNsPush`: 1 pushed, 0 not (a duplicate or redundant), -1.
    #[verifier::external_body]
    pub fn ns_push(&mut self, prefix: Option<&[u8]>, uri: &[u8], def_attr: bool) -> i32 {
        if prefix == Some(b"xml") {
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
            if self.options & (1 << 13) != 0 && self.nsdb.tab[old].uri == uri {
                return 0;
            }
        }
        let e = NsEntry { prefix: prefix.map(|p| p.to_vec()), uri: uri.to_vec(), element_id: self.nsdb.element_id };
        self.nsdb.tab.push(e);
        self.sink.ns_pushed(prefix, uri);
        1
    }

    /// `xmlParserNsPop`.
    #[verifier::external_body]
    pub fn ns_pop(&mut self, nr: usize) -> usize {
        let n = if nr < self.nsdb.tab.len() { nr } else { self.nsdb.tab.len() };
        let keep = self.nsdb.tab.len() - n;
        self.nsdb.tab.truncate(keep);
        if n > 0 {
            self.sink.ns_popped(n);
        }
        n
    }

    #[verifier::external_body]
    pub fn set_ns_min(&mut self, min: usize) {
        self.nsdb.min = min;
        self.sink.ns_min(min);
    }
}

} // verus!
