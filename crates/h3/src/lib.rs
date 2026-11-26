#![warn(missing_docs)]
#![doc = include_str!("../README.md")]
// Sans-I/O HTTP/3 (RFC 9114) framing, formally verified with Verus.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code))]
#[doc(hidden)]
pub mod encode;
#[doc(hidden)]
pub mod frame;
#[doc(hidden)]
pub mod lemmas;
#[doc(hidden)]
pub mod reader;
#[doc(hidden)]
pub mod spec;
#[doc(hidden)]
pub mod varint;

pub use encode::{
    header_size, settings_frame_size, write_header, write_id_frame, write_push_promise_head, write_settings, write_var,
};
pub use frame::{bidi_open_x as bidi_open, uni_closed_x as uni_closed, uni_kind_of as uni_kind, uni_open_x as uni_open};
pub use reader::{Event, Reader, Src};
pub use spec::{Settings, UniKind, UniSeen};
pub use varint::{read_var, var_size_of as var_size};

/// The frame types, stream types, settings and error codes of RFC 9114,
/// RFC 9204, RFC 9220 and RFC 9297.
pub mod consts {
    pub use crate::spec::{
        CANCEL_PUSH, DATA, GOAWAY, H3_CLOSED_CRITICAL_STREAM, H3_CONNECT_ERROR, H3_EXCESSIVE_LOAD, H3_FRAME_ERROR,
        H3_FRAME_UNEXPECTED, H3_GENERAL_PROTOCOL_ERROR, H3_ID_ERROR, H3_INTERNAL_ERROR, H3_MESSAGE_ERROR,
        H3_MISSING_SETTINGS, H3_NO_ERROR, H3_REQUEST_CANCELLED, H3_REQUEST_INCOMPLETE, H3_REQUEST_REJECTED,
        H3_SETTINGS_ERROR, H3_STREAM_CREATION_ERROR, H3_VERSION_FALLBACK, HEADERS, MAX_PUSH_ID, MAX_VARINT, PUSH_PROMISE,
        SETTINGS, SETTINGS_ENABLE_CONNECT_PROTOCOL, SETTINGS_H3_DATAGRAM, SETTINGS_MAX_FIELD_SECTION_SIZE,
        SETTINGS_QPACK_BLOCKED_STREAMS, SETTINGS_QPACK_MAX_TABLE_CAPACITY, STREAM_CONTROL, STREAM_PUSH,
        STREAM_QPACK_DECODER, STREAM_QPACK_ENCODER,
    };
}
