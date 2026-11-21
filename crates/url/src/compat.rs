//! An API shaped like the `url` crate's (`url::Url`), over vurl's verified
//! parser, so code written against `url` can switch by changing an import.
//!
//! Parsing decides acceptance with the verified parser. When it rejects an
//! input, `ParseError` names a likely reason, found by a separate diagnostic
//! pass ([`diagnose`]) that is plain Rust outside the proof: the reason is a
//! best effort, the rejection is not.
use crate::url::Url as Core;
use core::fmt;
use core::borrow::Borrow;
use core::str::FromStr;

/// Why an input did not parse, with the `url` crate's variants. vurl has no
/// 4 GB limit, so `Overflow` is never returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ParseError {
    EmptyHost,
    IdnaError,
    InvalidPort,
    InvalidIpv4Address,
    InvalidIpv6Address,
    InvalidDomainCharacter,
    RelativeUrlWithoutBase,
    RelativeUrlWithCannotBeABaseBase,
    SetHostOnCannotBeABaseUrl,
    Overflow,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ParseError::EmptyHost => "empty host",
            ParseError::IdnaError => "invalid international domain name",
            ParseError::InvalidPort => "invalid port number",
            ParseError::InvalidIpv4Address => "invalid IPv4 address",
            ParseError::InvalidIpv6Address => "invalid IPv6 address",
            ParseError::InvalidDomainCharacter => "invalid domain character",
            ParseError::RelativeUrlWithoutBase => "relative URL without a base",
            ParseError::RelativeUrlWithCannotBeABaseBase => "relative URL with a cannot-be-a-base base",
            ParseError::SetHostOnCannotBeABaseUrl => "a cannot-be-a-base URL doesn't have a host to set",
            ParseError::Overflow => "URLs more than 4 GB are not supported",
        })
    }
}

impl std::error::Error for ParseError {}

/// The host of a URL, as in the `url` crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Host<S = String> {
    Domain(S),
    Ipv4(std::net::Ipv4Addr),
    Ipv6(std::net::Ipv6Addr),
}

impl<S: AsRef<str>> fmt::Display for Host<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Host::Domain(d) => f.write_str(d.as_ref()),
            Host::Ipv4(a) => write!(f, "{a}"),
            Host::Ipv6(a) => write!(f, "[{a}]"),
        }
    }
}

/// A parsed URL. Equality, ordering and hashing compare the serialization.
#[derive(Clone)]
pub struct Url {
    inner: Core,
}

/// Options for parsing, as in the `url` crate (only the base is supported).
#[derive(Clone, Copy, Default)]
pub struct ParseOptions<'a> {
    base: Option<&'a Url>,
}

impl<'a> ParseOptions<'a> {
    pub fn base_url(mut self, base: Option<&'a Url>) -> Self {
        self.base = base;
        self
    }

    pub fn parse(self, input: &str) -> Result<Url, ParseError> {
        Url::parse_with(input, self.base)
    }
}

impl Url {
    /// Parses an absolute URL.
    pub fn parse(input: &str) -> Result<Url, ParseError> {
        Url::parse_with(input, None)
    }

    fn parse_with(input: &str, base: Option<&Url>) -> Result<Url, ParseError> {
        match Core::parse(input, base.map(|b| &b.inner)) {
            Some(inner) => Ok(Url { inner }),
            None => Err(diagnose(input, base.map(|b| &b.inner))),
        }
    }

    /// Parses an absolute URL from a string and query pairs to append.
    pub fn parse_with_params<I, K, V>(input: &str, iter: I) -> Result<Url, ParseError>
    where
        I: IntoIterator,
        I::Item: core::borrow::Borrow<(K, V)>,
        K: AsRef<str>,
        V: AsRef<str>,
    {
        let mut url = Url::parse(input)?;
        {
            let mut pairs = url.query_pairs_mut();
            for item in iter {
                let (k, v) = item.borrow();
                pairs.append_pair(k.as_ref(), v.as_ref());
            }
        }
        Ok(url)
    }

    pub fn options<'a>() -> ParseOptions<'a> {
        ParseOptions::default()
    }

    /// Parses `input` with this URL as the base.
    pub fn join(&self, input: &str) -> Result<Url, ParseError> {
        Url::parse_with(input, Some(self))
    }

    /// The verified core URL.
    pub fn as_core(&self) -> &Core {
        &self.inner
    }

    pub fn into_core(self) -> Core {
        self.inner
    }

    pub fn from_core(inner: Core) -> Url {
        Url { inner }
    }

    pub fn as_str(&self) -> &str {
        self.inner.href()
    }

    pub fn scheme(&self) -> &str {
        self.inner.scheme()
    }

    pub fn is_special(&self) -> bool {
        self.inner.is_special()
    }

    pub fn has_authority(&self) -> bool {
        self.inner.has_authority()
    }

    pub fn cannot_be_a_base(&self) -> bool {
        self.inner.has_opaque_path()
    }

    pub fn username(&self) -> &str {
        self.inner.username()
    }

    pub fn password(&self) -> Option<&str> {
        match self.inner.password() {
            "" => None,
            p => Some(p),
        }
    }

    /// Whether the URL has a non-empty host. Like the `url` crate, an empty
    /// host (as in "file:///x" or "sc://?") counts as no host.
    pub fn has_host(&self) -> bool {
        self.inner.has_authority() && !self.inner.hostname().is_empty()
    }

    /// The host as serialized ("[...]" for IPv6), or `None` without a host.
    pub fn host_str(&self) -> Option<&str> {
        if self.has_host() {
            Some(self.inner.hostname())
        } else {
            None
        }
    }

    pub fn host(&self) -> Option<Host<&str>> {
        let h = self.host_str()?;
        if let Some(v6) = h.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            return v6.parse().ok().map(Host::Ipv6);
        }
        if self.inner.is_special() {
            if let Ok(a) = h.parse() {
                return Some(Host::Ipv4(a));
            }
        }
        Some(Host::Domain(h))
    }

    /// The host if it is a domain (not an IP address).
    pub fn domain(&self) -> Option<&str> {
        match self.host()? {
            Host::Domain(d) => Some(d),
            _ => None,
        }
    }

    pub fn port(&self) -> Option<u16> {
        self.inner.port()
    }

    pub fn port_or_known_default(&self) -> Option<u16> {
        self.port().or(match self.scheme() {
            "http" | "ws" => Some(80),
            "https" | "wss" => Some(443),
            "ftp" => Some(21),
            _ => None,
        })
    }

    pub fn path(&self) -> &str {
        self.inner.pathname()
    }

    /// The path's segments, or `None` for a cannot-be-a-base URL.
    pub fn path_segments(&self) -> Option<core::str::Split<'_, char>> {
        let p = self.path();
        p.strip_prefix('/').map(|p| p.split('/'))
    }

    pub fn query(&self) -> Option<&str> {
        self.inner.query()
    }

    pub fn fragment(&self) -> Option<&str> {
        self.inner.fragment()
    }

    /// The query's name-value pairs, application/x-www-form-urlencoded
    /// decoded (a leading "?" in the query is part of the first name).
    pub fn query_pairs(&self) -> impl Iterator<Item = (String, String)> + '_ {
        let lossy = |b: Vec<u8>| String::from_utf8_lossy(&b).into_owned();
        let decode = crate::searchparams::form_decode;
        self.query().unwrap_or("").split('&').filter(|p| !p.is_empty()).map(move |p| {
            let (k, v) = p.split_once('=').unwrap_or((p, ""));
            (lossy(decode(k.as_bytes())), lossy(decode(v.as_bytes())))
        })
    }

    /// Appends to the query; the URL is updated when the returned value is
    /// dropped. Existing pairs are kept as written.
    pub fn query_pairs_mut(&mut self) -> QueryPairsMut<'_> {
        let query = self.query().unwrap_or("").to_owned();
        QueryPairsMut { url: self, query }
    }

    /// The ASCII serialization of the origin ("null" when opaque).
    pub fn origin_ascii(&self) -> String {
        self.inner.origin()
    }

    pub fn set_scheme(&mut self, scheme: &str) -> Result<(), ()> {
        let before = self.inner.scheme().to_owned();
        self.inner.set_protocol(scheme);
        if self.inner.scheme() == scheme.trim_end_matches(':') || scheme.is_empty() && before.is_empty() {
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn set_username(&mut self, username: &str) -> Result<(), ()> {
        if !self.can_have_credentials() {
            return Err(());
        }
        self.inner.set_username(username);
        Ok(())
    }

    pub fn set_password(&mut self, password: Option<&str>) -> Result<(), ()> {
        if !self.can_have_credentials() {
            return Err(());
        }
        self.inner.set_password(password.unwrap_or(""));
        Ok(())
    }

    fn can_have_credentials(&self) -> bool {
        self.inner.has_authority() && !self.inner.hostname().is_empty() && self.scheme() != "file"
    }

    /// Sets or removes the host (and, for `None`, the port and credentials).
    pub fn set_host(&mut self, host: Option<&str>) -> Result<(), ParseError> {
        if self.cannot_be_a_base() {
            return Err(ParseError::SetHostOnCannotBeABaseUrl);
        }
        match host {
            Some(h) => {
                if h.is_empty() && self.is_special() && self.scheme() != "file" {
                    return Err(ParseError::EmptyHost);
                }
                if self.inner.set_hostname(h) || self.inner.hostname() == h {
                    Ok(())
                } else {
                    Err(diagnose_host(h, self.is_special()))
                }
            }
            None => {
                if self.is_special() && self.scheme() != "file" {
                    return Err(ParseError::EmptyHost);
                }
                // Rebuild without the authority: "scheme:" + path + query + fragment.
                let mut s = String::from(self.inner.protocol());
                let path = self.path();
                if path.starts_with("//") {
                    s.push_str("/.");
                }
                s.push_str(path);
                if let Some(q) = self.query() {
                    s.push('?');
                    s.push_str(q);
                }
                if let Some(f) = self.fragment() {
                    s.push('#');
                    s.push_str(f);
                }
                match Core::parse(&s, None) {
                    Some(u) => {
                        self.inner = u;
                        Ok(())
                    }
                    None => Err(ParseError::EmptyHost),
                }
            }
        }
    }

    pub fn set_ip_host(&mut self, address: std::net::IpAddr) -> Result<(), ()> {
        let h = match address {
            std::net::IpAddr::V4(a) => a.to_string(),
            std::net::IpAddr::V6(a) => format!("[{a}]"),
        };
        self.set_host(Some(&h)).map_err(|_| ())
    }

    pub fn set_port(&mut self, port: Option<u16>) -> Result<(), ()> {
        if !self.inner.has_authority() || self.inner.hostname().is_empty() || self.scheme() == "file" {
            return Err(());
        }
        match port {
            Some(p) => {
                self.inner.set_port(&p.to_string());
            }
            None => {
                self.inner.set_port("");
            }
        }
        Ok(())
    }

    pub fn set_path(&mut self, path: &str) {
        self.inner.set_pathname(path);
    }

    pub fn set_query(&mut self, query: Option<&str>) {
        match query {
            Some(q) => {
                self.inner.set_search(q);
                if q.is_empty() && self.query().is_none() {
                    // "?" with an empty query: the search setter drops it.
                    let mut s = self.as_str().to_owned();
                    let at = s.find('#').unwrap_or(s.len());
                    s.insert(at, '?');
                    if let Some(u) = Core::parse(&s, None) {
                        self.inner = u;
                    }
                }
            }
            None => {
                self.inner.set_search("");
            }
        }
    }

    pub fn set_fragment(&mut self, fragment: Option<&str>) {
        match fragment {
            Some(f) => {
                self.inner.set_hash(f);
                if f.is_empty() && self.fragment().is_none() {
                    let s = format!("{}#", self.as_str());
                    if let Some(u) = Core::parse(&s, None) {
                        self.inner = u;
                    }
                }
            }
            None => self.inner.set_hash(""),
        }
    }
}

/// Appends or rewrites query pairs; see [`Url::query_pairs_mut`].
pub struct QueryPairsMut<'a> {
    url: &'a mut Url,
    query: String,
}

impl QueryPairsMut<'_> {
    pub fn append_pair(&mut self, name: &str, value: &str) -> &mut Self {
        let mut out = Vec::new();
        if !self.query.is_empty() {
            out.push(b'&');
        }
        crate::searchparams::form_encode(name.as_bytes(), &mut out);
        out.push(b'=');
        crate::searchparams::form_encode(value.as_bytes(), &mut out);
        self.query.push_str(core::str::from_utf8(&out).unwrap());
        self
    }

    pub fn extend_pairs<I, K, V>(&mut self, iter: I) -> &mut Self
    where
        I: IntoIterator,
        I::Item: core::borrow::Borrow<(K, V)>,
        K: AsRef<str>,
        V: AsRef<str>,
    {
        for item in iter {
            let (k, v) = item.borrow();
            self.append_pair(k.as_ref(), v.as_ref());
        }
        self
    }

    pub fn clear(&mut self) -> &mut Self {
        self.query.clear();
        self
    }
}

impl Drop for QueryPairsMut<'_> {
    fn drop(&mut self) {
        let q = core::mem::take(&mut self.query);
        self.url.set_query(Some(&q));
    }
}

impl fmt::Display for Url {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for Url {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Url")
            .field("scheme", &self.scheme())
            .field("cannot_be_a_base", &self.cannot_be_a_base())
            .field("username", &self.username())
            .field("password", &self.password())
            .field("host", &self.host_str())
            .field("port", &self.port())
            .field("path", &self.path())
            .field("query", &self.query())
            .field("fragment", &self.fragment())
            .finish()
    }
}

impl FromStr for Url {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Url, ParseError> {
        Url::parse(s)
    }
}

impl TryFrom<&str> for Url {
    type Error = ParseError;

    fn try_from(s: &str) -> Result<Url, ParseError> {
        Url::parse(s)
    }
}

impl AsRef<str> for Url {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl From<Url> for String {
    fn from(u: Url) -> String {
        u.as_str().to_owned()
    }
}

impl PartialEq for Url {
    fn eq(&self, other: &Url) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Url {}

impl PartialOrd for Url {
    fn partial_cmp(&self, other: &Url) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Url {
    fn cmp(&self, other: &Url) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl core::hash::Hash for Url {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

// ---------------------------------------------------------------------------
// Diagnosis of a rejected input (best effort, outside the proof)
// ---------------------------------------------------------------------------

/// A likely reason the parser rejected `input` against `base`. Only called
/// after the verified parser has rejected it.
pub fn diagnose(input: &str, base: Option<&Core>) -> ParseError {
    let s: String = input
        .trim_matches(|c: char| c <= ' ')
        .chars()
        .filter(|&c| c != '\t' && c != '\n' && c != '\r')
        .collect();
    let scheme_len = s
        .char_indices()
        .take_while(|&(i, c)| if i == 0 { c.is_ascii_alphabetic() } else { c.is_ascii_alphanumeric() || "+-.".contains(c) })
        .count();
    let has_scheme = scheme_len > 0 && s[scheme_len..].starts_with(':');
    let (scheme, rest) = if has_scheme {
        (s[..scheme_len].to_ascii_lowercase(), &s[scheme_len + 1..])
    } else {
        match base {
            None => return ParseError::RelativeUrlWithoutBase,
            Some(b) if b.has_opaque_path() => return ParseError::RelativeUrlWithCannotBeABaseBase,
            Some(b) => (b.scheme().to_owned(), &s[..]),
        }
    };
    let special = matches!(scheme.as_str(), "http" | "https" | "ws" | "wss" | "ftp" | "file");
    let slash = |c: char| c == '/' || (special && c == '\\');
    let after = rest.trim_start_matches(slash);
    if !has_scheme && rest.len() - after.len() < 2 && !special {
        return ParseError::RelativeUrlWithoutBase;
    }
    let auth_end = after.find(|c: char| slash(c) || c == '?' || c == '#').unwrap_or(after.len());
    let authority = &after[..auth_end];
    let hostport = match authority.rfind('@') {
        Some(i) => &authority[i + 1..],
        None => authority,
    };
    let (host, port) = if scheme == "file" {
        // A file URL has no port, so a ':' is part of the host.
        (hostport, None)
    } else if hostport.starts_with('[') {
        match hostport.find(']') {
            Some(i) => (&hostport[..=i], hostport[i + 1..].strip_prefix(':')),
            None => return ParseError::InvalidIpv6Address,
        }
    } else {
        match hostport.find(':') {
            Some(i) => (&hostport[..i], Some(&hostport[i + 1..])),
            None => (hostport, None),
        }
    };
    if host.is_empty() {
        return ParseError::EmptyHost;
    }
    if let Some(p) = port {
        if !p.is_empty() && (!p.bytes().all(|c| c.is_ascii_digit()) || p.parse::<u32>().map_or(true, |n| n > 65535)) {
            return ParseError::InvalidPort;
        }
    }
    diagnose_host(host, special)
}

fn diagnose_host(host: &str, special: bool) -> ParseError {
    if host.starts_with('[') {
        return ParseError::InvalidIpv6Address;
    }
    if !special {
        return ParseError::InvalidDomainCharacter;
    }
    let decoded = crate::searchparams::form_decode(host.replace('+', "%2B").as_bytes());
    if !decoded.is_ascii() {
        return ParseError::IdnaError;
    }
    let lower = String::from_utf8_lossy(&decoded).to_ascii_lowercase();
    let last = lower.trim_end_matches('.').rsplit('.').next().unwrap_or("");
    let numeric = !last.is_empty()
        && (last.bytes().all(|c| c.is_ascii_digit())
            || (last.starts_with("0x") && last[2..].bytes().all(|c| c.is_ascii_hexdigit())));
    if numeric {
        return ParseError::InvalidIpv4Address;
    }
    // The Standard rejects these as forbidden domain code points after
    // UTS 46 mapping; like the url crate, report them as IDNA errors.
    ParseError::IdnaError
}
