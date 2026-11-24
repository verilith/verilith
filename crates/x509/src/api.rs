//! Unverified conveniences on top of the verified parser: `Iterator`
//! impls, string views and time conversion. None of it reads untrusted
//! bytes except through the verified functions.
use crate::cert::Certificate;
use crate::der::Tlv;
use crate::ext::Extension;
use crate::iter::*;
use crate::time::Time;
use crate::x509::{Atv, GeneralName, Name};
use core::fmt;

macro_rules! iterator {
    ($t:ident, $item:ty) => {
        impl<'a> Iterator for $t<'a> {
            type Item = $item;
            #[inline]
            fn next(&mut self) -> Option<$item> {
                $t::next(self)
            }
        }
    };
}

iterator!(RdnIter, Rdn<'a>);
iterator!(AtvIter, Atv<'a>);
iterator!(GeneralNameIter, GeneralName<'a>);
iterator!(SubtreeIter, GeneralName<'a>);
iterator!(OidIter, &'a [u8]);
iterator!(ExtensionIter, Extension<'a>);
iterator!(PolicyIter, &'a [u8]);

impl<'a> Name<'a> {
    /// The RelativeDistinguishedNames, in order.
    pub fn rdns(&self) -> RdnIter<'a> {
        RdnIter::new(self)
    }

    /// Every attribute of every RDN, in order.
    pub fn attributes(&self) -> impl Iterator<Item = Atv<'a>> + 'a + use<'a> {
        self.rdns().flat_map(|r| r.attributes())
    }
}

impl<'a> Rdn<'a> {
    /// The attributes of this RDN, in order.
    pub fn attributes(&self) -> AtvIter<'a> {
        AtvIter::new(self)
    }
}

impl<'a> Atv<'a> {
    /// The value as text, for the string types X.520 uses, when it is valid
    /// in its type's character set as decoded here (UTF8String must be valid
    /// UTF-8; BMPString and UniversalString are not decoded).
    pub fn value_str(&self) -> Option<&'a str> {
        match self.value.tag {
            [0x0C] | [0x13] | [0x16] | [0x14] | [0x1A] => core::str::from_utf8(self.value.content).ok(),
            _ => None,
        }
    }
}

/// Dotted-decimal text for OID contents octets (`2.5.4.3`), without
/// allocating: `format!("{}", OidDisplay(oid))`. Arcs that do not fit in a
/// `u128` are written as `?`.
#[derive(Clone, Copy)]
pub struct OidDisplay<'a>(pub &'a [u8]);

impl fmt::Display for OidDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut v: Option<u128> = Some(0);
        let mut first = true;
        for &b in self.0 {
            v = v.and_then(|x| x.checked_mul(128)).map(|x| x | (b & 0x7F) as u128);
            if b & 0x80 != 0 {
                continue;
            }
            let arc = |f: &mut fmt::Formatter<'_>, a: Option<u128>| match a {
                Some(x) => write!(f, "{x}"),
                None => f.write_str("?"),
            };
            if first {
                match v {
                    Some(x) if x < 80 => write!(f, "{}.{}", x / 40, x % 40)?,
                    Some(x) => write!(f, "2.{}", x - 80)?,
                    None => f.write_str("2.?")?,
                }
                first = false;
            } else {
                f.write_str(".")?;
                arc(f, v)?;
            }
            v = Some(0);
        }
        Ok(())
    }
}

/// Dotted-decimal text for OID contents octets (`2.5.4.3`). Arcs that do not
/// fit in a `u128` are written as `?`.
#[cfg(feature = "alloc")]
pub fn oid_to_string(oid: &[u8]) -> alloc::string::String {
    alloc::format!("{}", OidDisplay(oid))
}

/// Bytes as a string when they are UTF-8, otherwise as hex.
struct Text<'a>(&'a [u8]);

impl fmt::Debug for Text<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match core::str::from_utf8(self.0) {
            Ok(s) => write!(f, "{s:?}"),
            Err(_) => write!(f, "{:02x?}", self.0),
        }
    }
}

impl<'a> fmt::Debug for Tlv<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tlv({:02x?}, {} octets)", self.tag, self.content.len())
    }
}

impl<'a> fmt::Debug for GeneralName<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = Text;
        match self {
            GeneralName::Other { type_id, value } => write!(f, "Other({}, {:?})", OidDisplay(type_id), value),
            GeneralName::Rfc822(b) => write!(f, "Rfc822({:?})", s(b)),
            GeneralName::Dns(b) => write!(f, "Dns({:?})", s(b)),
            GeneralName::X400(b) => write!(f, "X400({} octets)", b.len()),
            GeneralName::Directory(_) => write!(f, "Directory(..)"),
            GeneralName::EdiParty(b) => write!(f, "EdiParty({} octets)", b.len()),
            GeneralName::Uri(b) => write!(f, "Uri({:?})", s(b)),
            GeneralName::Ip(b) => write!(f, "Ip({:?})", b),
            GeneralName::Registered(b) => write!(f, "Registered({})", OidDisplay(b)),
        }
    }
}

impl Time {
    /// Seconds since 1970-01-01T00:00:00Z (negative before it).
    pub fn unix_timestamp(&self) -> i64 {
        // Days from civil (Howard Hinnant's algorithm).
        let (y, m, d) = (self.year as i64, self.month as i64, self.day as i64);
        let y = if m <= 2 { y - 1 } else { y };
        let era = y.div_euclid(400);
        let yoe = y - era * 400;
        let mp = (m + 9) % 12;
        let doy = (153 * mp + 2) / 5 + d - 1;
        let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
        let days = era * 146097 + doe - 719468;
        days * 86400 + self.hour as i64 * 3600 + self.minute as i64 * 60 + self.second as i64
    }
}

impl<'a> Certificate<'a> {
    /// Parses one DER certificate (the verified [`crate::cert::parse`]).
    pub fn from_der(b: &'a [u8]) -> Option<Certificate<'a>> {
        crate::cert::parse(b)
    }

    /// The issuer's Name.
    pub fn issuer(&self) -> Name<'a> {
        self.tbs.issuer
    }

    /// The subject's Name.
    pub fn subject(&self) -> Name<'a> {
        self.tbs.subject
    }

    /// 0 for v1, 1 for v2, 2 for v3.
    pub fn version(&self) -> u8 {
        self.tbs.version
    }

    /// The serial number INTEGER's contents (two's complement, minimal).
    pub fn serial(&self) -> &'a [u8] {
        self.tbs.serial
    }

    /// The start of the validity period.
    pub fn not_before(&self) -> Time {
        self.tbs.not_before
    }

    /// The end of the validity period.
    pub fn not_after(&self) -> Time {
        self.tbs.not_after
    }

    /// DNS names in the subjectAltName extension.
    pub fn dns_names(&self) -> impl Iterator<Item = &'a [u8]> + 'a + use<'a> {
        self.subject_alt_names().into_iter().flatten().filter_map(|g| match g {
            GeneralName::Dns(d) => Some(d),
            _ => None,
        })
    }
}
