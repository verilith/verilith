//! Which requests in TLS 0-RTT data are answered (RFC 8470), verified.
//!
//! Early data can be replayed (RFC 8446 §8), so a request in it is handed
//! to the handler only if its method is one of the safe methods (RFC 9110
//! §9.2.1) that browsers send early, GET, HEAD and OPTIONS (`early_safe`);
//! any other gets 425 Too Early (RFC 8470 §5.2) and the client sends it
//! again after the handshake. [`too_early`] decides it, exactly.
use vstd::prelude::*;

verus! {

/// "GET"
pub open spec fn m_get() -> Seq<u8> {
    seq![0x47u8, 0x45, 0x54]
}

/// "HEAD"
pub open spec fn m_head() -> Seq<u8> {
    seq![0x48u8, 0x45, 0x41, 0x44]
}

/// "OPTIONS"
pub open spec fn m_options() -> Seq<u8> {
    seq![0x4fu8, 0x50, 0x54, 0x49, 0x4f, 0x4e, 0x53]
}

/// The methods taken in early data: safe (RFC 9110 §9.2.1), and the ones
/// browsers send early. Methods are case-sensitive (RFC 9110 §9.1).
pub open spec fn early_safe(m: Seq<u8>) -> bool {
    m == m_get() || m == m_head() || m == m_options()
}

/// Whether `m` is one of the methods taken in early data.
pub fn early_ok(m: &[u8]) -> (r: bool)
    ensures
        r == early_safe(m@),
{
    let n = m.len();
    let r = if n == 3 {
        m[0] == 0x47 && m[1] == 0x45 && m[2] == 0x54
    } else if n == 4 {
        m[0] == 0x48 && m[1] == 0x45 && m[2] == 0x41 && m[3] == 0x44
    } else if n == 7 {
        m[0] == 0x4f && m[1] == 0x50 && m[2] == 0x54 && m[3] == 0x49 && m[4] == 0x4f && m[5] == 0x4e && m[6]
            == 0x53
    } else {
        false
    };
    proof {
        if r {
            if n == 3 {
                assert(m@ =~= m_get());
            } else if n == 4 {
                assert(m@ =~= m_head());
            } else {
                assert(m@ =~= m_options());
            }
        }
        if early_safe(m@) {
            if m@ == m_get() {
                assert(m@[0] == 0x47 && m@[1] == 0x45 && m@[2] == 0x54);
            } else if m@ == m_head() {
                assert(m@[0] == 0x48 && m@[1] == 0x45 && m@[2] == 0x41 && m@[3] == 0x44);
            } else {
                assert(m@[0] == 0x4f && m@[1] == 0x50 && m@[2] == 0x54 && m@[3] == 0x49);
                assert(m@[4] == 0x4f && m@[5] == 0x4e && m@[6] == 0x53);
            }
        }
    }
    r
}

/// Whether a request with method `m` is answered 425 Too Early instead of
/// being handed to the handler: it came in early data and its method is
/// not one of `early_safe`'s.
pub fn too_early(early: bool, m: &[u8]) -> (r: bool)
    ensures
        r == (early && !early_safe(m@)),
{
    early && !early_ok(m)
}

} // verus!
