//! Frames (§7): the verified header reader, the frame-order checks, the
//! payload parsers, and the encoders.
use crate::spec::*;
use crate::varint::*;
use vstd::prelude::*;

verus! {

/// The kind of frame type `t`.
#[inline(always)]
pub fn kind_of(t: u64) -> (r: Kind)
    ensures
        r == kind(t as nat),
{
    match t {
        DATA => Kind::Data,
        HEADERS => Kind::Headers,
        CANCEL_PUSH => Kind::CancelPush,
        SETTINGS => Kind::Settings,
        PUSH_PROMISE => Kind::PushPromise,
        GOAWAY => Kind::Goaway,
        MAX_PUSH_ID => Kind::MaxPushId,
        0x02 | 0x06 | 0x08 | 0x09 => Kind::H2,
        _ => Kind::Other,
    }
}

/// Whether `k` is read whole.
#[inline(always)]
pub fn is_buffered(k: Kind) -> (r: bool)
    ensures
        r == buffered(k),
{
    !matches!(k, Kind::Data | Kind::Other | Kind::H2)
}

/// The kind of unidirectional stream type `t`.
#[inline(always)]
pub fn uni_kind_of(t: u64) -> (r: UniKind)
    ensures
        r == uni_kind(t as nat),
{
    match t {
        STREAM_CONTROL => UniKind::Control,
        STREAM_PUSH => UniKind::Push,
        STREAM_QPACK_ENCODER => UniKind::QpackEncoder,
        STREAM_QPACK_DECODER => UniKind::QpackDecoder,
        _ => UniKind::Other,
    }
}

pub proof fn lemma_skip_skip(s: Seq<u8>, a: int, b: int)
    requires
        0 <= a,
        0 <= b,
        a + b <= s.len(),
    ensures
        s.skip(a).skip(b) == s.skip(a + b),
{
    assert(s.skip(a).skip(b) =~= s.skip(a + b));
}

/// Reads the frame header at `b[p..]`: its type, payload length and end.
#[inline(always)]
pub fn read_hdr(b: &[u8], p: usize) -> (r: Option<(u64, u64, usize)>)
    requires
        p <= b@.len(),
    ensures
        match hdr_dec(b@.skip(p as int)) {
            Hdr::Short => r is None,
            Hdr::Ok(t, len, h) => r matches Some((rt, rl, e)) && rt as nat == t && rl as nat == len && e as nat == p + h,
        },
        r matches Some((t, len, e)) ==> t <= MAX_VARINT && len <= MAX_VARINT && p + 2 <= e <= b@.len() && e <= p + 16,
{
    match read_var(b, p) {
        None => None,
        Some((t, e1)) => {
            let ghost s = b@.skip(p as int);
            proof {
                lemma_skip_skip(b@, p as int, e1 - p);
                assert(var_dec(s) is Ok);
                assert(var_dec(s)->Ok_0 <= MAX_VARINT);
                assert(var_dec(s)->Ok_0 as u64 == t);
                assert(var_dec(s)->Ok_0 == t as nat);
                assert(var_dec(s)->Ok_1 == (e1 - p) as nat);
                assert(var_dec(s) == Var::Ok(t as nat, (e1 - p) as nat));
            }
            match read_var(b, e1) {
                None => {
                    assert(var_dec(s.skip(e1 - p)) is Short);
                    None
                },
                Some((len, e2)) => {
                    assert(var_dec(s.skip(e1 - p)) == Var::Ok(len as nat, (e2 - e1) as nat));
                    assert(hdr_dec(s) == Hdr::Ok(t as nat, len as nat, (e2 - p) as nat));
                    Some((t, len, e2))
                },
            }
        },
    }
}

/// `accept`, in code.
#[inline(always)]
pub fn accept_x(o: Order, server: bool, limit: u64, t: u64, len: u64) -> (r: Result<Order, u64>)
    ensures
        r == accept(o, server, limit as nat, t as nat, len as nat),
{
    let k = kind_of(t);
    match o {
        Order::Control { settings, goaway, max_push } => {
            if !settings {
                if !matches!(k, Kind::Settings) {
                    Err(H3_MISSING_SETTINGS)
                } else if len > limit {
                    Err(H3_EXCESSIVE_LOAD)
                } else {
                    Ok(Order::Control { settings: true, goaway, max_push })
                }
            } else {
                match k {
                    Kind::CancelPush | Kind::Goaway => {
                        if len == 0 || len > 8 {
                            Err(H3_FRAME_ERROR)
                        } else {
                            Ok(o)
                        }
                    },
                    Kind::MaxPushId => {
                        if !server {
                            Err(H3_FRAME_UNEXPECTED)
                        } else if len == 0 || len > 8 {
                            Err(H3_FRAME_ERROR)
                        } else {
                            Ok(o)
                        }
                    },
                    Kind::Other => Ok(o),
                    _ => Err(H3_FRAME_UNEXPECTED),
                }
            }
        },
        Order::Request(p) | Order::Response(p) | Order::Push(p) => {
            match k {
                Kind::Data => match p {
                    Phase::Head | Phase::Body => Ok(phase_x(o, Phase::Body)),
                    _ => Err(H3_FRAME_UNEXPECTED),
                },
                Kind::Headers => {
                    if matches!(p, Phase::Done) {
                        Err(H3_FRAME_UNEXPECTED)
                    } else if len > limit {
                        Err(H3_EXCESSIVE_LOAD)
                    } else if matches!(p, Phase::Start) {
                        Ok(phase_x(o, Phase::Head))
                    } else if matches!(p, Phase::Head) && !matches!(o, Order::Request(_)) {
                        Ok(o)
                    } else {
                        Ok(phase_x(o, Phase::Done))
                    }
                },
                Kind::PushPromise => {
                    if !matches!(o, Order::Response(_)) {
                        Err(H3_FRAME_UNEXPECTED)
                    } else if len > limit {
                        Err(H3_EXCESSIVE_LOAD)
                    } else {
                        Ok(o)
                    }
                },
                Kind::Other => Ok(o),
                _ => Err(H3_FRAME_UNEXPECTED),
            }
        },
    }
}

#[inline(always)]
fn phase_x(o: Order, p: Phase) -> (r: Order)
    ensures
        r == with_phase(o, p),
{
    match o {
        Order::Request(_) => Order::Request(p),
        Order::Response(_) => Order::Response(p),
        Order::Push(_) => Order::Push(p),
        Order::Control { .. } => o,
    }
}

/// `setting`, in code.
#[inline(always)]
pub fn setting_x(acc: Settings, id: u64, v: u64) -> (r: Result<Settings, u64>)
    ensures
        r == setting(acc, id as nat, v as nat),
{
    if id == 0x00 || id == 0x02 || id == 0x03 || id == 0x04 || id == 0x05 {
        Err(H3_SETTINGS_ERROR)
    } else if id == SETTINGS_QPACK_MAX_TABLE_CAPACITY {
        if acc.qpack_max_table_capacity.is_some() {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { qpack_max_table_capacity: Some(v), ..acc })
        }
    } else if id == SETTINGS_MAX_FIELD_SECTION_SIZE {
        if acc.max_field_section_size.is_some() {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { max_field_section_size: Some(v), ..acc })
        }
    } else if id == SETTINGS_QPACK_BLOCKED_STREAMS {
        if acc.qpack_blocked_streams.is_some() {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { qpack_blocked_streams: Some(v), ..acc })
        }
    } else if id == SETTINGS_ENABLE_CONNECT_PROTOCOL {
        if acc.enable_connect_protocol.is_some() || v > 1 {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { enable_connect_protocol: Some(v), ..acc })
        }
    } else if id == SETTINGS_H3_DATAGRAM {
        if acc.h3_datagram.is_some() || v > 1 {
            Err(H3_SETTINGS_ERROR)
        } else {
            Ok(Settings { h3_datagram: Some(v), ..acc })
        }
    } else {
        Ok(acc)
    }
}

/// Parses a SETTINGS payload. The ghost result counts the loop's turns:
/// at most one per two bytes, plus one.
pub fn parse_settings(p: &[u8]) -> (r: (Result<Settings, u64>, Ghost<nat>))
    ensures
        r.0 == settings_dec(p@),
        2 * r.1@ <= p@.len() + 2,
{
    let mut acc = Settings {
        qpack_max_table_capacity: None,
        max_field_section_size: None,
        qpack_blocked_streams: None,
        enable_connect_protocol: None,
        h3_datagram: None,
    };
    let mut pos: usize = 0;
    let ghost mut turns: nat = 0;
    let len = p.len();
    proof {
        assert(p@.skip(0) =~= p@);
    }
    while pos < len
        invariant
            pos <= p@.len(),
            len == p@.len(),
            settings_dec(p@) == settings_from(p@.skip(pos as int), acc),
            2 * turns <= pos,
        decreases p@.len() - pos,
    {
        let ghost s = p@.skip(pos as int);
        match read_var(p, pos) {
            None => return (Err(H3_FRAME_ERROR), Ghost(turns + 1)),
            Some((id, e1)) => {
                proof {
                    lemma_skip_skip(p@, pos as int, e1 - pos);
                }
                match read_var(p, e1) {
                    None => return (Err(H3_FRAME_ERROR), Ghost(turns + 1)),
                    Some((v, e2)) => {
                        proof {
                            lemma_skip_skip(p@, pos as int, e2 - pos);
                        }
                        match setting_x(acc, id, v) {
                            Err(e) => return (Err(e), Ghost(turns + 1)),
                            Ok(a2) => {
                                acc = a2;
                            },
                        }
                        pos = e2;
                    },
                }
            },
        }
        proof {
            turns = turns + 1;
        }
    }
    (Ok(acc), Ghost(turns))
}

/// What a completed buffered frame reports, with the field section of a
/// PUSH_PROMISE as an offset into its payload.
#[derive(Clone, Copy)]
pub enum CEv {
    Headers,
    PushPromise(u64, usize),
    Settings(Settings),
    CancelPush(u64),
    Goaway(u64),
    MaxPushId(u64),
}

pub open spec fn cev_view(c: CEv, p: Seq<u8>) -> Ev {
    match c {
        CEv::Headers => Ev::Headers(p),
        CEv::PushPromise(id, off) => Ev::PushPromise(id, p.skip(off as int)),
        CEv::Settings(s) => Ev::Settings(s),
        CEv::CancelPush(v) => Ev::CancelPush(v),
        CEv::Goaway(v) => Ev::Goaway(v),
        CEv::MaxPushId(v) => Ev::MaxPushId(v),
    }
}

/// `single`, in code.
#[inline(always)]
fn single_x(p: &[u8]) -> (r: Option<u64>)
    ensures
        match single(p@) {
            None => r is None,
            Some(v) => r matches Some(rv) && rv as nat == v,
        },
        r matches Some(v) ==> v <= MAX_VARINT,
{
    proof {
        assert(p@.skip(0) =~= p@);
    }
    match read_var(p, 0) {
        Some((v, e)) => {
            if e == p.len() {
                Some(v)
            } else {
                None
            }
        },
        None => None,
    }
}

/// `complete`, in code; the ghost result counts loop turns (SETTINGS').
pub fn complete_x(o: Order, server: bool, k: Kind, p: &[u8]) -> (r: (Result<(Order, CEv), u64>, Ghost<nat>))
    requires
        buffered(k),
    ensures
        match complete(o, server, k, p@) {
            Err(e) => r.0 == Err::<(Order, CEv), u64>(e),
            Ok((o3, ev)) => r.0 matches Ok((o4, c)) && o4 == o3 && cev_view(c, p@) == ev && (c matches CEv::PushPromise(_, off) ==> off <= p@.len()),
        },
        2 * r.1@ <= p@.len() + 2,
{
    match k {
        Kind::Headers => (Ok((o, CEv::Headers)), Ghost(0)),
        Kind::PushPromise => {
            proof {
                assert(p@.skip(0) =~= p@);
            }
            match read_var(p, 0) {
                None => (Err(H3_FRAME_ERROR), Ghost(0)),
                Some((id, n)) => (Ok((o, CEv::PushPromise(id, n))), Ghost(0)),
            }
        },
        Kind::Settings => {
            let (s, g) = parse_settings(p);
            match s {
                Err(e) => (Err(e), g),
                Ok(s) => (Ok((o, CEv::Settings(s))), g),
            }
        },
        _ => {
            let v = match single_x(p) {
                None => return (Err(H3_FRAME_ERROR), Ghost(0)),
                Some(v) => v,
            };
            match o {
                Order::Control { settings, goaway, max_push } => {
                    if matches!(k, Kind::CancelPush) {
                        if server && (max_push.is_none() || v > max_push.unwrap()) {
                            (Err(H3_ID_ERROR), Ghost(0))
                        } else {
                            (Ok((o, CEv::CancelPush(v))), Ghost(0))
                        }
                    } else if matches!(k, Kind::Goaway) {
                        if (!server && v % 4 != 0) || (goaway.is_some() && v > goaway.unwrap()) {
                            (Err(H3_ID_ERROR), Ghost(0))
                        } else {
                            (Ok((Order::Control { settings, goaway: Some(v), max_push }, CEv::Goaway(v))), Ghost(0))
                        }
                    } else {
                        if max_push.is_some() && v < max_push.unwrap() {
                            (Err(H3_ID_ERROR), Ghost(0))
                        } else {
                            (Ok((Order::Control { settings, goaway, max_push: Some(v) }, CEv::MaxPushId(v))), Ghost(0))
                        }
                    }
                },
                _ => (Err(H3_FRAME_UNEXPECTED), Ghost(0)),
            }
        },
    }
}

} // verus!
