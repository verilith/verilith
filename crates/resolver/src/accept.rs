//! Which responses are taken as the answer to a query: `spec::response_ok`.
use crate::rr::bytes_eq;
use crate::spec::*;
use verilith_dns::Message;
use vstd::prelude::*;

verus! {

/// `response_ok(m, id, qname, qtype)`: the response has the query's ID and
/// exactly its question (name byte for byte), and is a response to a
/// standard query.
pub fn response_matches(m: &Message, id: u16, qname: &[u8], qtype: u16) -> (r: bool)
    ensures
        r == response_ok(m@, id, qname@, qtype),
{
    let f = m.flags();
    if m.id() != id || f < 0x8000 || (f / 0x0800) % 16 != 0 || m.question_count() != 1 {
        return false;
    }
    let q = m.question(0).unwrap();
    bytes_eq(q.name, qname) && q.qtype == qtype && q.qclass == CLASS_IN
}

} // verus!
