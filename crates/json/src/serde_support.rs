//! serde support (the `serde` feature): [`from_slice`], [`from_str`],
//! [`to_vec`], [`to_vec_pretty`] and [`to_string`].
//!
//! Deserialization runs the verified parser, then walks its tape. Strings
//! without escapes are borrowed from the input, so `&str` fields work.
//! Serialization goes through [`Writer`], whose string escaping is proven
//! to round-trip. As in serde_json, NaN and infinities are written as
//! `null`, bytes as arrays of numbers, and enums externally tagged.
use crate::parser::{ex_decode, Kind, Tok};
use crate::writer::{WriteError, Writer};
use ::serde::de::{self, DeserializeSeed, IntoDeserializer, Visitor};
use ::serde::{ser, Deserialize, Serialize};
use std::fmt;

/// A serde error: invalid JSON, a value of the wrong shape, or a value
/// that cannot be written.
#[derive(Debug)]
pub enum Error {
    Parse(crate::Error),
    Write(WriteError),
    Message(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(e) => e.fmt(f),
            Error::Write(e) => e.fmt(f),
            Error::Message(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for Error {}

impl de::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Error {
        Error::Message(msg.to_string())
    }
}

impl ser::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Error {
        Error::Message(msg.to_string())
    }
}

impl From<WriteError> for Error {
    fn from(e: WriteError) -> Error {
        Error::Write(e)
    }
}

// ---------------------------------------------------------------------------
// Deserializing
// ---------------------------------------------------------------------------

/// Deserializes a `T` from a JSON text.
pub fn from_slice<'de, T: Deserialize<'de>>(input: &'de [u8]) -> Result<T, Error> {
    // serde copies decoded strings out anyway, so decode them on demand.
    let doc = crate::value::parse_mode(input, false).map_err(Error::Parse)?;
    let mut d = Deserializer { src: input, tape: doc.tape(), idx: 0 };
    T::deserialize(&mut d)
}

/// Deserializes a `T` from a JSON text.
pub fn from_str<'de, T: Deserialize<'de>>(input: &'de str) -> Result<T, Error> {
    from_slice(input.as_bytes())
}

/// A deserializer over a parsed tape, positioned at one value.
struct Deserializer<'de, 't> {
    src: &'de [u8],
    tape: &'t [Tok],
    idx: usize,
}

enum Text<'de> {
    Borrowed(&'de str),
    Owned(String),
}

impl<'de> Deserializer<'de, '_> {
    fn tok(&self) -> Tok {
        self.tape[self.idx]
    }

    fn text(&self, t: Tok) -> Result<Text<'de>, Error> {
        let (a, b) = (t.start(), t.end());
        // The parser has checked that the text is UTF-8, and decoding keeps
        // it so; `from_utf8` checks again.
        let bad = || Error::Message("string is not UTF-8".into());
        if t.escaped {
            let mut out = Vec::with_capacity(b - a);
            ex_decode(self.src, a, b, &mut out);
            String::from_utf8(out).map(Text::Owned).map_err(|_| bad())
        } else {
            std::str::from_utf8(&self.src[a..b]).map(Text::Borrowed).map_err(|_| bad())
        }
    }

    fn number(&self, t: Tok) -> &'de [u8] {
        &self.src[t.start()..t.end()]
    }

    /// The index after the value at `idx`.
    fn skip(&self) -> usize {
        let t = self.tok();
        match t.kind {
            Kind::ArrStart | Kind::ObjStart => t.start() + 1,
            _ => self.idx + 1,
        }
    }

    /// The number here as a 128-bit integer, consumed, if it is one.
    fn int128<T: std::str::FromStr>(&mut self) -> Option<T> {
        let t = self.tok();
        if t.kind != Kind::Num {
            return None;
        }
        let n = std::str::from_utf8(self.number(t)).ok()?.parse().ok()?;
        self.idx += 1;
        Some(n)
    }

    fn unexpected(&self) -> de::Unexpected<'static> {
        match self.tok().kind {
            Kind::Null => de::Unexpected::Unit,
            Kind::True => de::Unexpected::Bool(true),
            Kind::False => de::Unexpected::Bool(false),
            Kind::Num => de::Unexpected::Other("number"),
            Kind::Str | Kind::Key => de::Unexpected::Other("string"),
            Kind::ArrStart | Kind::ArrEnd => de::Unexpected::Seq,
            Kind::ObjStart | Kind::ObjEnd => de::Unexpected::Map,
        }
    }
}

fn visit_number<'de, V: Visitor<'de>>(lex: &[u8], v: V) -> Result<V::Value, Error> {
    // As in serde_json, `-0` is the float -0.0.
    let integral = !lex.iter().any(|&c| matches!(c, b'.' | b'e' | b'E')) && lex != b"-0";
    if integral {
        if let Some(n) = crate::number::parse_i64(lex) {
            return if n < 0 { v.visit_i64(n) } else { v.visit_u64(n as u64) };
        }
        if let Some(n) = std::str::from_utf8(lex).ok().and_then(|s| s.parse::<u64>().ok()) {
            return v.visit_u64(n);
        }
    }
    v.visit_f64(crate::number::parse_f64(lex))
}

impl<'de> de::Deserializer<'de> for &mut Deserializer<'de, '_> {
    type Error = Error;

    fn deserialize_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        let t = self.tok();
        match t.kind {
            Kind::Null => {
                self.idx += 1;
                v.visit_unit()
            }
            Kind::True | Kind::False => {
                self.idx += 1;
                v.visit_bool(t.kind == Kind::True)
            }
            Kind::Num => {
                self.idx += 1;
                visit_number(self.number(t), v)
            }
            Kind::Str | Kind::Key => {
                self.idx += 1;
                match self.text(t)? {
                    Text::Borrowed(s) => v.visit_borrowed_str(s),
                    Text::Owned(s) => v.visit_string(s),
                }
            }
            Kind::ArrStart => {
                let end = t.start();
                self.idx += 1;
                let r = v.visit_seq(Seq { d: &mut *self, end })?;
                if self.idx != end {
                    return Err(de::Error::custom("array has more elements than expected"));
                }
                self.idx = end + 1;
                Ok(r)
            }
            Kind::ObjStart => {
                let end = t.start();
                self.idx += 1;
                let r = v.visit_map(Map { d: &mut *self, end })?;
                if self.idx != end {
                    return Err(de::Error::custom("object has more members than expected"));
                }
                self.idx = end + 1;
                Ok(r)
            }
            Kind::ArrEnd | Kind::ObjEnd => Err(de::Error::custom("expected a value")),
        }
    }

    fn deserialize_option<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        if self.tok().kind == Kind::Null {
            self.idx += 1;
            v.visit_none()
        } else {
            v.visit_some(self)
        }
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(self, _name: &'static str, v: V) -> Result<V::Value, Error> {
        v.visit_newtype_struct(self)
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        v: V,
    ) -> Result<V::Value, Error> {
        let t = self.tok();
        match t.kind {
            // A unit variant, by name.
            Kind::Str => {
                self.idx += 1;
                let name = match self.text(t)? {
                    Text::Borrowed(s) => s.to_owned(),
                    Text::Owned(s) => s,
                };
                v.visit_enum(name.into_deserializer())
            }
            // `{"Variant": value}`.
            Kind::ObjStart => {
                let end = t.start();
                self.idx += 1;
                if self.idx == end {
                    return Err(de::Error::custom("expected an enum variant, found an empty object"));
                }
                let r = v.visit_enum(Enum { d: &mut *self })?;
                if self.idx != end {
                    return Err(de::Error::custom("expected one member in an enum variant object"));
                }
                self.idx = end + 1;
                Ok(r)
            }
            _ => Err(de::Error::invalid_type(self.unexpected(), &"an enum")),
        }
    }

    fn deserialize_ignored_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        self.idx = self.skip();
        v.visit_unit()
    }

    fn deserialize_i128<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        match self.int128::<i128>() {
            Some(n) => v.visit_i128(n),
            None => self.deserialize_any(v),
        }
    }

    fn deserialize_u128<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        match self.int128::<u128>() {
            Some(n) => v.visit_u128(n),
            None => self.deserialize_any(v),
        }
    }

    ::serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 char str string
        bytes byte_buf unit unit_struct seq tuple tuple_struct map struct identifier
    }
}

struct Seq<'a, 'de, 't> {
    d: &'a mut Deserializer<'de, 't>,
    end: usize,
}

impl<'de> de::SeqAccess<'de> for Seq<'_, 'de, '_> {
    type Error = Error;

    fn next_element_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<Option<T::Value>, Error> {
        if self.d.idx >= self.end {
            return Ok(None);
        }
        seed.deserialize(&mut *self.d).map(Some)
    }
}

struct Map<'a, 'de, 't> {
    d: &'a mut Deserializer<'de, 't>,
    end: usize,
}

impl<'de> de::MapAccess<'de> for Map<'_, 'de, '_> {
    type Error = Error;

    fn next_key_seed<K: DeserializeSeed<'de>>(&mut self, seed: K) -> Result<Option<K::Value>, Error> {
        if self.d.idx >= self.end {
            return Ok(None);
        }
        seed.deserialize(Key { d: &mut *self.d }).map(Some)
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(&mut self, seed: V) -> Result<V::Value, Error> {
        seed.deserialize(&mut *self.d)
    }
}

/// An object member name. Besides strings, it reads integers written as
/// strings, for maps with integer keys.
struct Key<'a, 'de, 't> {
    d: &'a mut Deserializer<'de, 't>,
}

macro_rules! key_int {
    ($($f:ident $t:ty => $visit:ident),*) => {$(
        fn $f<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
            let t = self.d.tok();
            self.d.idx += 1;
            let s = match self.d.text(t)? {
                Text::Borrowed(s) => s.to_owned(),
                Text::Owned(s) => s,
            };
            match s.parse::<$t>() {
                Ok(n) => v.$visit(n),
                Err(_) => Err(de::Error::invalid_value(de::Unexpected::Str(&s), &"an integer")),
            }
        }
    )*};
}

impl<'de> de::Deserializer<'de> for Key<'_, 'de, '_> {
    type Error = Error;

    fn deserialize_any<V: Visitor<'de>>(self, v: V) -> Result<V::Value, Error> {
        self.d.deserialize_any(v)
    }

    key_int! {
        deserialize_i8 i8 => visit_i8, deserialize_i16 i16 => visit_i16,
        deserialize_i32 i32 => visit_i32, deserialize_i64 i64 => visit_i64,
        deserialize_u8 u8 => visit_u8, deserialize_u16 u16 => visit_u16,
        deserialize_u32 u32 => visit_u32, deserialize_u64 u64 => visit_u64
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(self, _name: &'static str, v: V) -> Result<V::Value, Error> {
        v.visit_newtype_struct(self)
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        v: V,
    ) -> Result<V::Value, Error> {
        self.d.deserialize_enum(name, variants, v)
    }

    ::serde::forward_to_deserialize_any! {
        bool i128 u128 f32 f64 char str string bytes byte_buf option unit
        unit_struct seq tuple tuple_struct map struct identifier ignored_any
    }
}

struct Enum<'a, 'de, 't> {
    d: &'a mut Deserializer<'de, 't>,
}

impl<'de> de::EnumAccess<'de> for Enum<'_, 'de, '_> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self), Error> {
        let v = seed.deserialize(Key { d: &mut *self.d })?;
        Ok((v, self))
    }
}

impl<'de> de::VariantAccess<'de> for Enum<'_, 'de, '_> {
    type Error = Error;

    fn unit_variant(self) -> Result<(), Error> {
        Deserialize::deserialize(&mut *self.d)
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, seed: T) -> Result<T::Value, Error> {
        seed.deserialize(&mut *self.d)
    }

    fn tuple_variant<V: Visitor<'de>>(self, _len: usize, v: V) -> Result<V::Value, Error> {
        de::Deserializer::deserialize_seq(&mut *self.d, v)
    }

    fn struct_variant<V: Visitor<'de>>(self, _fields: &'static [&'static str], v: V) -> Result<V::Value, Error> {
        de::Deserializer::deserialize_map(&mut *self.d, v)
    }
}

// ---------------------------------------------------------------------------
// Serializing
// ---------------------------------------------------------------------------

/// Serializes `value` as compact JSON.
pub fn to_vec<T: Serialize + ?Sized>(value: &T) -> Result<Vec<u8>, Error> {
    let mut s = Serializer { w: Writer::new() };
    value.serialize(&mut s)?;
    Ok(s.w.finish()?)
}

/// Serializes `value` with each element and member on its own line,
/// indented by two spaces.
pub fn to_vec_pretty<T: Serialize + ?Sized>(value: &T) -> Result<Vec<u8>, Error> {
    let mut s = Serializer { w: Writer::pretty(2) };
    value.serialize(&mut s)?;
    Ok(s.w.finish()?)
}

/// Serializes `value` as compact JSON.
pub fn to_string<T: Serialize + ?Sized>(value: &T) -> Result<String, Error> {
    // The writer emits UTF-8: strings come from `&str`, and everything it
    // adds is ASCII.
    to_vec(value).map(|v| String::from_utf8(v).expect("the writer emits UTF-8"))
}

struct Serializer {
    w: Writer,
}

impl<'a> ser::Serializer for &'a mut Serializer {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Compound<'a>;
    type SerializeTuple = Compound<'a>;
    type SerializeTupleStruct = Compound<'a>;
    type SerializeTupleVariant = Compound<'a>;
    type SerializeMap = Compound<'a>;
    type SerializeStruct = Compound<'a>;
    type SerializeStructVariant = Compound<'a>;

    fn serialize_bool(self, b: bool) -> Result<(), Error> {
        Ok(self.w.bool(b)?)
    }
    fn serialize_i8(self, n: i8) -> Result<(), Error> {
        Ok(self.w.i64(n.into())?)
    }
    fn serialize_i16(self, n: i16) -> Result<(), Error> {
        Ok(self.w.i64(n.into())?)
    }
    fn serialize_i32(self, n: i32) -> Result<(), Error> {
        Ok(self.w.i64(n.into())?)
    }
    fn serialize_i64(self, n: i64) -> Result<(), Error> {
        Ok(self.w.i64(n)?)
    }
    fn serialize_i128(self, n: i128) -> Result<(), Error> {
        Ok(self.w.number_str(&n.to_string())?)
    }
    fn serialize_u8(self, n: u8) -> Result<(), Error> {
        Ok(self.w.u64(n.into())?)
    }
    fn serialize_u16(self, n: u16) -> Result<(), Error> {
        Ok(self.w.u64(n.into())?)
    }
    fn serialize_u32(self, n: u32) -> Result<(), Error> {
        Ok(self.w.u64(n.into())?)
    }
    fn serialize_u64(self, n: u64) -> Result<(), Error> {
        Ok(self.w.u64(n)?)
    }
    fn serialize_u128(self, n: u128) -> Result<(), Error> {
        Ok(self.w.number_str(&n.to_string())?)
    }
    fn serialize_f32(self, x: f32) -> Result<(), Error> {
        if !x.is_finite() {
            return Ok(self.w.null()?);
        }
        // The shortest form that reads back as this `f32`.
        Ok(self.w.number_str(crate::writer::float_text(x, &mut zmij::Buffer::new()))?)
    }
    fn serialize_f64(self, x: f64) -> Result<(), Error> {
        if !x.is_finite() {
            return Ok(self.w.null()?);
        }
        Ok(self.w.f64(x)?)
    }
    fn serialize_char(self, c: char) -> Result<(), Error> {
        Ok(self.w.string(c.encode_utf8(&mut [0; 4]))?)
    }
    fn serialize_str(self, s: &str) -> Result<(), Error> {
        Ok(self.w.string(s)?)
    }
    fn serialize_bytes(self, b: &[u8]) -> Result<(), Error> {
        self.w.begin_array()?;
        for &x in b {
            self.w.u64(x.into())?;
        }
        Ok(self.w.end_array()?)
    }
    fn serialize_none(self) -> Result<(), Error> {
        Ok(self.w.null()?)
    }
    fn serialize_some<T: Serialize + ?Sized>(self, v: &T) -> Result<(), Error> {
        v.serialize(self)
    }
    fn serialize_unit(self) -> Result<(), Error> {
        Ok(self.w.null()?)
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<(), Error> {
        Ok(self.w.null()?)
    }
    fn serialize_unit_variant(self, _name: &'static str, _i: u32, variant: &'static str) -> Result<(), Error> {
        Ok(self.w.string(variant)?)
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(self, _name: &'static str, v: &T) -> Result<(), Error> {
        v.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _i: u32,
        variant: &'static str,
        v: &T,
    ) -> Result<(), Error> {
        self.w.begin_object()?;
        self.w.key(variant)?;
        v.serialize(&mut *self)?;
        Ok(self.w.end_object()?)
    }
    fn serialize_seq(self, _len: Option<usize>) -> Result<Compound<'a>, Error> {
        self.w.begin_array()?;
        Ok(Compound { s: self, close: Close::Array })
    }
    fn serialize_tuple(self, len: usize) -> Result<Compound<'a>, Error> {
        self.serialize_seq(Some(len))
    }
    fn serialize_tuple_struct(self, _name: &'static str, len: usize) -> Result<Compound<'a>, Error> {
        self.serialize_seq(Some(len))
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _i: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Compound<'a>, Error> {
        self.w.begin_object()?;
        self.w.key(variant)?;
        self.w.begin_array()?;
        Ok(Compound { s: self, close: Close::ArrayInObject })
    }
    fn serialize_map(self, _len: Option<usize>) -> Result<Compound<'a>, Error> {
        self.w.begin_object()?;
        Ok(Compound { s: self, close: Close::Object })
    }
    fn serialize_struct(self, _name: &'static str, len: usize) -> Result<Compound<'a>, Error> {
        self.serialize_map(Some(len))
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _i: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Compound<'a>, Error> {
        self.w.begin_object()?;
        self.w.key(variant)?;
        self.w.begin_object()?;
        Ok(Compound { s: self, close: Close::ObjectInObject })
    }
}

enum Close {
    Array,
    ArrayInObject,
    Object,
    ObjectInObject,
}

struct Compound<'a> {
    s: &'a mut Serializer,
    close: Close,
}

impl Compound<'_> {
    fn end(self) -> Result<(), Error> {
        let w = &mut self.s.w;
        match self.close {
            Close::Array => w.end_array()?,
            Close::ArrayInObject => {
                w.end_array()?;
                w.end_object()?
            }
            Close::Object => w.end_object()?,
            Close::ObjectInObject => {
                w.end_object()?;
                w.end_object()?
            }
        }
        Ok(())
    }

    fn element<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        v.serialize(&mut *self.s)
    }

    fn member<T: Serialize + ?Sized>(&mut self, k: &str, v: &T) -> Result<(), Error> {
        self.s.w.key(k)?;
        v.serialize(&mut *self.s)
    }
}

impl ser::SerializeSeq for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        self.element(v)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

impl ser::SerializeTuple for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        self.element(v)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

impl ser::SerializeTupleStruct for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        self.element(v)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

impl ser::SerializeTupleVariant for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        self.element(v)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

impl ser::SerializeMap for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, k: &T) -> Result<(), Error> {
        k.serialize(KeyName { w: &mut self.s.w })
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Error> {
        v.serialize(&mut *self.s)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

impl ser::SerializeStruct for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, k: &'static str, v: &T) -> Result<(), Error> {
        self.member(k, v)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

impl ser::SerializeStructVariant for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, k: &'static str, v: &T) -> Result<(), Error> {
        self.member(k, v)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}

/// Writes a map key as a member name: strings as they are, and integers,
/// booleans and chars as their text, as serde_json does.
struct KeyName<'a> {
    w: &'a mut Writer,
}

fn key_error() -> Error {
    Error::Message("map key must be a string, integer, bool or char".into())
}

macro_rules! key_display {
    ($($f:ident $t:ty),*) => {$(
        fn $f(self, n: $t) -> Result<(), Error> {
            Ok(self.w.key(&n.to_string())?)
        }
    )*};
}

impl ser::Serializer for KeyName<'_> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = ser::Impossible<(), Error>;
    type SerializeTuple = ser::Impossible<(), Error>;
    type SerializeTupleStruct = ser::Impossible<(), Error>;
    type SerializeTupleVariant = ser::Impossible<(), Error>;
    type SerializeMap = ser::Impossible<(), Error>;
    type SerializeStruct = ser::Impossible<(), Error>;
    type SerializeStructVariant = ser::Impossible<(), Error>;

    key_display! {
        serialize_bool bool, serialize_i8 i8, serialize_i16 i16, serialize_i32 i32,
        serialize_i64 i64, serialize_i128 i128, serialize_u8 u8, serialize_u16 u16,
        serialize_u32 u32, serialize_u64 u64, serialize_u128 u128, serialize_char char
    }

    fn serialize_f32(self, _x: f32) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_f64(self, _x: f64) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_str(self, s: &str) -> Result<(), Error> {
        Ok(self.w.key(s)?)
    }
    fn serialize_bytes(self, _b: &[u8]) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_none(self) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_some<T: Serialize + ?Sized>(self, _v: &T) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_unit(self) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_unit_variant(self, _name: &'static str, _i: u32, variant: &'static str) -> Result<(), Error> {
        Ok(self.w.key(variant)?)
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(self, _name: &'static str, v: &T) -> Result<(), Error> {
        v.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _i: u32,
        _variant: &'static str,
        _v: &T,
    ) -> Result<(), Error> {
        Err(key_error())
    }
    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Error> {
        Err(key_error())
    }
    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Error> {
        Err(key_error())
    }
    fn serialize_tuple_struct(self, _name: &'static str, _len: usize) -> Result<Self::SerializeTupleStruct, Error> {
        Err(key_error())
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _i: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Error> {
        Err(key_error())
    }
    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Error> {
        Err(key_error())
    }
    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Self::SerializeStruct, Error> {
        Err(key_error())
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _i: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Error> {
        Err(key_error())
    }
}
