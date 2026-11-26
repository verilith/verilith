//! Transport parameters (§18): the verified parser and encoder.
//!
//! [`parse`] reads the transport parameters a peer sent in its TLS
//! handshake (the quic_transport_parameters extension, which the trusted
//! TLS layer extracts), and [`encode`] writes ours. The proofs: `parse` is
//! `spec::transport_params`, `encode` is `spec::transport_params_enc`, and
//! valid parameters read back from their encoding
//! (`lemmas::lemma_transport_params_roundtrip`).
use crate::spec::*;
use crate::varint;
use verilith_core::prims::extend;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A preferred_address value (§18.2).
#[derive(Clone, Copy)]
pub struct PreferredAddress<'a> {
    /// IPv4 address and port (6 bytes).
    pub v4: &'a [u8],
    /// IPv6 address and port (18 bytes).
    pub v6: &'a [u8],
    /// Connection ID (1 to 20 bytes).
    pub cid: &'a [u8],
    /// Stateless reset token (16 bytes).
    pub token: &'a [u8],
}

impl<'a> PreferredAddress<'a> {
    /// The value as `spec::SPref`.
    pub open spec fn view(self) -> SPref {
        SPref { v4: self.v4@, v6: self.v6@, cid: self.cid@, token: self.token@ }
    }
}

/// Transport parameters (§18.2), each absent or with its value, borrowing
/// from the encoded parameters. Absent parameters take the defaults of
/// §18.2, which the accessors below apply.
#[derive(Clone, Copy)]
pub struct TransportParameters<'a> {
    /// 0x00: original_destination_connection_id.
    pub original_dcid: Option<&'a [u8]>,
    /// 0x01: max_idle_timeout (milliseconds).
    pub max_idle_timeout: Option<u64>,
    /// 0x02: stateless_reset_token (16 bytes).
    pub stateless_reset_token: Option<&'a [u8]>,
    /// 0x03: max_udp_payload_size, at least 1200.
    pub max_udp_payload_size: Option<u64>,
    /// 0x04: initial_max_data.
    pub initial_max_data: Option<u64>,
    /// 0x05: initial_max_stream_data_bidi_local.
    pub initial_max_stream_data_bidi_local: Option<u64>,
    /// 0x06: initial_max_stream_data_bidi_remote.
    pub initial_max_stream_data_bidi_remote: Option<u64>,
    /// 0x07: initial_max_stream_data_uni.
    pub initial_max_stream_data_uni: Option<u64>,
    /// 0x08: initial_max_streams_bidi, at most 2^60.
    pub initial_max_streams_bidi: Option<u64>,
    /// 0x09: initial_max_streams_uni, at most 2^60.
    pub initial_max_streams_uni: Option<u64>,
    /// 0x0a: ack_delay_exponent, at most 20.
    pub ack_delay_exponent: Option<u64>,
    /// 0x0b: max_ack_delay (milliseconds), below 2^14.
    pub max_ack_delay: Option<u64>,
    /// 0x0c: disable_active_migration.
    pub disable_active_migration: bool,
    /// 0x0d: preferred_address.
    pub preferred_address: Option<PreferredAddress<'a>>,
    /// 0x0e: active_connection_id_limit, at least 2.
    pub active_connection_id_limit: Option<u64>,
    /// 0x0f: initial_source_connection_id.
    pub initial_scid: Option<&'a [u8]>,
    /// 0x10: retry_source_connection_id.
    pub retry_scid: Option<&'a [u8]>,
    /// 0x20: max_datagram_frame_size (RFC 9221).
    pub max_datagram_frame_size: Option<u64>,
}

impl<'a> TransportParameters<'a> {
    /// The parameters as `spec::TP`.
    pub open spec fn view(self) -> TP {
        TP {
            original_dcid: match self.original_dcid { None => None, Some(s) => Some(s@) },
            max_idle_timeout: self.max_idle_timeout,
            stateless_reset_token: match self.stateless_reset_token { None => None, Some(s) => Some(s@) },
            max_udp_payload_size: self.max_udp_payload_size,
            initial_max_data: self.initial_max_data,
            initial_max_stream_data_bidi_local: self.initial_max_stream_data_bidi_local,
            initial_max_stream_data_bidi_remote: self.initial_max_stream_data_bidi_remote,
            initial_max_stream_data_uni: self.initial_max_stream_data_uni,
            initial_max_streams_bidi: self.initial_max_streams_bidi,
            initial_max_streams_uni: self.initial_max_streams_uni,
            ack_delay_exponent: self.ack_delay_exponent,
            max_ack_delay: self.max_ack_delay,
            disable_active_migration: self.disable_active_migration,
            preferred_address: match self.preferred_address { None => None, Some(a) => Some(a@) },
            active_connection_id_limit: self.active_connection_id_limit,
            initial_scid: match self.initial_scid { None => None, Some(s) => Some(s@) },
            retry_scid: match self.retry_scid { None => None, Some(s) => Some(s@) },
            max_datagram_frame_size: self.max_datagram_frame_size,
        }
    }

    /// No parameters.
    pub fn new() -> (r: Self)
        ensures
            r@ == tp_empty(),
    {
        TransportParameters {
            original_dcid: None,
            max_idle_timeout: None,
            stateless_reset_token: None,
            max_udp_payload_size: None,
            initial_max_data: None,
            initial_max_stream_data_bidi_local: None,
            initial_max_stream_data_bidi_remote: None,
            initial_max_stream_data_uni: None,
            initial_max_streams_bidi: None,
            initial_max_streams_uni: None,
            ack_delay_exponent: None,
            max_ack_delay: None,
            disable_active_migration: false,
            preferred_address: None,
            active_connection_id_limit: None,
            initial_scid: None,
            retry_scid: None,
            max_datagram_frame_size: None,
        }
    }
}

/// An integer parameter's value.
#[inline(always)]
fn read_int(v: &[u8]) -> (r: Option<u64>)
    ensures
        r == tp_int(v@),
{
    match varint::read(v, 0) {
        Some((x, e)) => if e == v.len() {
            Some(x)
        } else {
            None
        },
        None => None,
    }
}

/// A preferred_address value.
fn read_pref<'a>(v: &'a [u8]) -> (r: Option<PreferredAddress<'a>>)
    ensures
        match (r, pref_parse(v@)) {
            (None, None) => true,
            (Some(a), Some(sa)) => a@ == sa,
            _ => false,
        },
{
    if v.len() < 41 || v[24] < 1 || v[24] > 20 || v.len() != 41 + v[24] as usize {
        return None;
    }
    let n = v[24] as usize;
    Some(PreferredAddress {
        v4: slice_subrange(v, 0, 6),
        v6: slice_subrange(v, 6, 24),
        cid: slice_subrange(v, 25, 25 + n),
        token: slice_subrange(v, 25 + n, v.len()),
    })
}

/// Adds parameter `id` with value `v` to `t`: `spec::tp_apply`.
#[verifier::rlimit(60)]
fn apply<'a>(t: &mut TransportParameters<'a>, id: u64, v: &'a [u8]) -> (ok: bool)
    ensures
        match tp_apply(old(t)@, id, v@) {
            None => !ok,
            Some(a) => ok && final(t)@ == a,
        },
{
    if id == 0x00 {
        if t.original_dcid.is_some() || v.len() as u64 > MAX_CID_LEN {
            return false;
        }
        t.original_dcid = Some(v);
        true
    } else if id == 0x01 {
        if t.max_idle_timeout.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                t.max_idle_timeout = Some(x);
                true
            },
        }
    } else if id == 0x02 {
        if t.stateless_reset_token.is_some() || v.len() != 16 {
            return false;
        }
        t.stateless_reset_token = Some(v);
        true
    } else if id == 0x03 {
        if t.max_udp_payload_size.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                if !(x >= 1200) {
                    return false;
                }
                t.max_udp_payload_size = Some(x);
                true
            },
        }
    } else if id == 0x04 {
        if t.initial_max_data.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                t.initial_max_data = Some(x);
                true
            },
        }
    } else if id == 0x05 {
        if t.initial_max_stream_data_bidi_local.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                t.initial_max_stream_data_bidi_local = Some(x);
                true
            },
        }
    } else if id == 0x06 {
        if t.initial_max_stream_data_bidi_remote.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                t.initial_max_stream_data_bidi_remote = Some(x);
                true
            },
        }
    } else if id == 0x07 {
        if t.initial_max_stream_data_uni.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                t.initial_max_stream_data_uni = Some(x);
                true
            },
        }
    } else if id == 0x08 {
        if t.initial_max_streams_bidi.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                if !(x <= MAX_STREAMS_LIMIT) {
                    return false;
                }
                t.initial_max_streams_bidi = Some(x);
                true
            },
        }
    } else if id == 0x09 {
        if t.initial_max_streams_uni.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                if !(x <= MAX_STREAMS_LIMIT) {
                    return false;
                }
                t.initial_max_streams_uni = Some(x);
                true
            },
        }
    } else if id == 0x0a {
        if t.ack_delay_exponent.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                if !(x <= 20) {
                    return false;
                }
                t.ack_delay_exponent = Some(x);
                true
            },
        }
    } else if id == 0x0b {
        if t.max_ack_delay.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                if !(x < 0x4000) {
                    return false;
                }
                t.max_ack_delay = Some(x);
                true
            },
        }
    } else if id == 0x0c {
        if t.disable_active_migration || v.len() != 0 {
            return false;
        }
        t.disable_active_migration = true;
        true
    } else if id == 0x0d {
        if t.preferred_address.is_some() {
            return false;
        }
        match read_pref(v) {
            None => false,
            Some(a) => {
                t.preferred_address = Some(a);
                true
            },
        }
    } else if id == 0x0e {
        if t.active_connection_id_limit.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                if !(x >= 2) {
                    return false;
                }
                t.active_connection_id_limit = Some(x);
                true
            },
        }
    } else if id == 0x0f {
        if t.initial_scid.is_some() || v.len() as u64 > MAX_CID_LEN {
            return false;
        }
        t.initial_scid = Some(v);
        true
    } else if id == 0x10 {
        if t.retry_scid.is_some() || v.len() as u64 > MAX_CID_LEN {
            return false;
        }
        t.retry_scid = Some(v);
        true
    } else if id == 0x20 {
        if t.max_datagram_frame_size.is_some() {
            return false;
        }
        match read_int(v) {
            None => false,
            Some(x) => {
                t.max_datagram_frame_size = Some(x);
                true
            },
        }
    } else {
        true
    }
}

/// Parses transport parameters (§18): `spec::transport_params`. `None` is a
/// connection error of type TRANSPORT_PARAMETER_ERROR.
pub fn parse<'a>(b: &'a [u8]) -> (r: Option<TransportParameters<'a>>)
    ensures
        match (r, transport_params(b@)) {
            (None, None) => true,
            (Some(t), Some(st)) => t@ == st,
            _ => false,
        },
{
    let mut t = TransportParameters::new();
    let mut p: usize = 0;
    while p < b.len()
        invariant
            p <= b@.len(),
            transport_params(b@) == tp_parse(b@, p as int, t@),
        decreases b@.len() - p,
    {
        let (id, p1) = match varint::read(b, p) {
            None => return None,
            Some(x) => x,
        };
        let (n, p2) = match varint::read(b, p1) {
            None => return None,
            Some(x) => x,
        };
        if n > (b.len() - p2) as u64 {
            return None;
        }
        let e = p2 + n as usize;
        let v = slice_subrange(b, p2, e);
        if !apply(&mut t, id, v) {
            return None;
        }
        p = e;
    }
    Some(t)
}

/// The parameters only a server may send are absent (§18.2):
/// `spec::tp_client_ok`. A server checks this of its client's.
pub fn client_ok(t: &TransportParameters) -> (r: bool)
    ensures
        r == tp_client_ok(t@),
{
    t.original_dcid.is_none() && t.stateless_reset_token.is_none() && t.preferred_address.is_none()
        && t.retry_scid.is_none()
}

/// Appends one parameter whose value is `v`.
#[inline(always)]
fn write_entry(out: &mut Vec<u8>, id: u64, v: &[u8])
    requires
        vi(id),
        v@.len() < VARINT_LIMIT,
    ensures
        final(out)@ == old(out)@ + tp_entry_enc(id, v@),
{
    varint::write(out, id);
    varint::write(out, v.len() as u64);
    extend(out, v);
    proof {
        assert(final(out)@ =~= old(out)@ + tp_entry_enc(id, v@));
    }
}

/// Appends one integer parameter.
#[inline(always)]
fn write_int(out: &mut Vec<u8>, id: u64, x: u64)
    requires
        vi(id),
        vi(x),
    ensures
        final(out)@ == old(out)@ + tp_entry_enc(id, varint_enc(x)),
{
    varint::write(out, id);
    varint::write(out, varint::size(x) as u64);
    varint::write(out, x);
    proof {
        crate::varint::lemma_varint_roundtrip(x, Seq::empty(), Seq::empty());
        assert(final(out)@ =~= old(out)@ + tp_entry_enc(id, varint_enc(x)));
    }
}

/// Appends a preferred_address parameter.
fn write_pref(out: &mut Vec<u8>, a: &PreferredAddress)
    requires
        a.v4@.len() == 6,
        a.v6@.len() == 18,
        1 <= a.cid@.len() <= 20,
        a.token@.len() == 16,
    ensures
        final(out)@ == old(out)@ + tp_entry_enc(0x0d, pref_enc(a@)),
{
    varint::write(out, 0x0d);
    varint::write(out, (41 + a.cid.len()) as u64);
    extend(out, a.v4);
    extend(out, a.v6);
    out.push(a.cid.len() as u8);
    extend(out, a.cid);
    extend(out, a.token);
    proof {
        assert(final(out)@ =~= old(out)@ + tp_entry_enc(0x0d, pref_enc(a@)));
    }
}

#[inline(always)]
fn put_original_dcid(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 0),
{
    let ghost o = old(out)@;
    if let Some(v) = t.original_dcid {
        write_entry(out, 0x00, v);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 0));
    }
}

#[inline(always)]
fn put_max_idle_timeout(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 1),
{
    let ghost o = old(out)@;
    if let Some(x) = t.max_idle_timeout {
        write_int(out, 0x01, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 1));
    }
}

#[inline(always)]
fn put_stateless_reset_token(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 2),
{
    let ghost o = old(out)@;
    if let Some(v) = t.stateless_reset_token {
        write_entry(out, 0x02, v);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 2));
    }
}

#[inline(always)]
fn put_max_udp_payload_size(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 3),
{
    let ghost o = old(out)@;
    if let Some(x) = t.max_udp_payload_size {
        write_int(out, 0x03, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 3));
    }
}

#[inline(always)]
fn put_initial_max_data(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 4),
{
    let ghost o = old(out)@;
    if let Some(x) = t.initial_max_data {
        write_int(out, 0x04, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 4));
    }
}

#[inline(always)]
fn put_initial_max_stream_data_bidi_local(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 5),
{
    let ghost o = old(out)@;
    if let Some(x) = t.initial_max_stream_data_bidi_local {
        write_int(out, 0x05, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 5));
    }
}

#[inline(always)]
fn put_initial_max_stream_data_bidi_remote(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 6),
{
    let ghost o = old(out)@;
    if let Some(x) = t.initial_max_stream_data_bidi_remote {
        write_int(out, 0x06, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 6));
    }
}

#[inline(always)]
fn put_initial_max_stream_data_uni(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 7),
{
    let ghost o = old(out)@;
    if let Some(x) = t.initial_max_stream_data_uni {
        write_int(out, 0x07, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 7));
    }
}

#[inline(always)]
fn put_initial_max_streams_bidi(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 8),
{
    let ghost o = old(out)@;
    if let Some(x) = t.initial_max_streams_bidi {
        write_int(out, 0x08, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 8));
    }
}

#[inline(always)]
fn put_initial_max_streams_uni(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 9),
{
    let ghost o = old(out)@;
    if let Some(x) = t.initial_max_streams_uni {
        write_int(out, 0x09, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 9));
    }
}

#[inline(always)]
fn put_ack_delay_exponent(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 10),
{
    let ghost o = old(out)@;
    if let Some(x) = t.ack_delay_exponent {
        write_int(out, 0x0a, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 10));
    }
}

#[inline(always)]
fn put_max_ack_delay(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 11),
{
    let ghost o = old(out)@;
    if let Some(x) = t.max_ack_delay {
        write_int(out, 0x0b, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 11));
    }
}

#[inline(always)]
fn put_disable_active_migration(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 12),
{
    let ghost o = old(out)@;
    if t.disable_active_migration {
        varint::write(out, 0x0c);
        varint::write(out, 0);
        proof {
            assert(varint_enc(0) =~= seq![0u8]);
            assert(bytes_len_enc(Seq::empty()) =~= seq![0u8]);
        }
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 12));
    }
}

#[inline(always)]
fn put_preferred_address(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 13),
{
    let ghost o = old(out)@;
    if let Some(a) = &t.preferred_address {
        write_pref(out, a);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 13));
    }
}

#[inline(always)]
fn put_active_connection_id_limit(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 14),
{
    let ghost o = old(out)@;
    if let Some(x) = t.active_connection_id_limit {
        write_int(out, 0x0e, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 14));
    }
}

#[inline(always)]
fn put_initial_scid(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 15),
{
    let ghost o = old(out)@;
    if let Some(v) = t.initial_scid {
        write_entry(out, 0x0f, v);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 15));
    }
}

#[inline(always)]
fn put_retry_scid(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 16),
{
    let ghost o = old(out)@;
    if let Some(v) = t.retry_scid {
        write_entry(out, 0x10, v);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 16));
    }
}

#[inline(always)]
fn put_max_datagram_frame_size(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + tp_field_enc(t@, 17),
{
    let ghost o = old(out)@;
    if let Some(x) = t.max_datagram_frame_size {
        write_int(out, 0x20, x);
    }
    proof {
        assert(out@ =~= o + tp_field_enc(t@, 17));
    }
}

/// Appends the encoding of `t` (`spec::transport_params_enc`) to `out`.
pub fn encode(t: &TransportParameters, out: &mut Vec<u8>)
    requires
        tp_wf(t@),
    ensures
        final(out)@ == old(out)@ + transport_params_enc(t@),
{
    let ghost o = old(out)@;
    proof {
        assert(out@ =~= o + crate::lemmas::tp_enc_upto(t@, 0));
    }
    let ghost b0 = out@;
    put_original_dcid(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b0, out@, t@, 0);
    }
    let ghost b1 = out@;
    put_max_idle_timeout(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b1, out@, t@, 1);
    }
    let ghost b2 = out@;
    put_stateless_reset_token(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b2, out@, t@, 2);
    }
    let ghost b3 = out@;
    put_max_udp_payload_size(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b3, out@, t@, 3);
    }
    let ghost b4 = out@;
    put_initial_max_data(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b4, out@, t@, 4);
    }
    let ghost b5 = out@;
    put_initial_max_stream_data_bidi_local(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b5, out@, t@, 5);
    }
    let ghost b6 = out@;
    put_initial_max_stream_data_bidi_remote(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b6, out@, t@, 6);
    }
    let ghost b7 = out@;
    put_initial_max_stream_data_uni(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b7, out@, t@, 7);
    }
    let ghost b8 = out@;
    put_initial_max_streams_bidi(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b8, out@, t@, 8);
    }
    let ghost b9 = out@;
    put_initial_max_streams_uni(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b9, out@, t@, 9);
    }
    let ghost b10 = out@;
    put_ack_delay_exponent(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b10, out@, t@, 10);
    }
    let ghost b11 = out@;
    put_max_ack_delay(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b11, out@, t@, 11);
    }
    let ghost b12 = out@;
    put_disable_active_migration(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b12, out@, t@, 12);
    }
    let ghost b13 = out@;
    put_preferred_address(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b13, out@, t@, 13);
    }
    let ghost b14 = out@;
    put_active_connection_id_limit(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b14, out@, t@, 14);
    }
    let ghost b15 = out@;
    put_initial_scid(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b15, out@, t@, 15);
    }
    let ghost b16 = out@;
    put_retry_scid(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b16, out@, t@, 16);
    }
    let ghost b17 = out@;
    put_max_datagram_frame_size(t, out);
    proof {
        crate::lemmas::lemma_tp_enc_step(o, b17, out@, t@, 17);
    }
    proof {
        crate::lemmas::lemma_tp_enc_upto_all(t@);
    }
}

} // verus!
