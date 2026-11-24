//! The public Rust API: parsing and the URL Standard's getters.
//!
//! The getters slice the verified `href` at the verified component offsets
//! (`Url::wf`); they are plain Rust.
use crate::url::Url;

impl Url {
    /// Parses `input` against an optional base URL, as the URL Standard's
    /// API URL parser does. Returns `None` on failure.
    pub fn parse(input: &str, base: Option<&Url>) -> Option<Url> {
        crate::api::parse(input.as_bytes(), base)
    }

    /// Parses raw bytes (treated as UTF-8; invalid sequences can only end
    /// up percent-encoded or rejected).
    pub fn parse_bytes(input: &[u8], base: Option<&Url>) -> Option<Url> {
        crate::api::parse(input, base)
    }

    /// Whether `input` parses against `base`.
    pub fn can_parse(input: &str, base: Option<&Url>) -> bool {
        Self::parse(input, base).is_some()
    }

    fn s(&self, a: usize, b: usize) -> &str {
        let s = &self.href[a..b];
        // SAFETY: `href` is ASCII, so every slice of it is UTF-8. The
        // parser proves it (`api::parse` ensures `Url::ok`, and
        // `url::lemma_ok_href_ascii` turns that into an ASCII href); the
        // setters build URLs with `set::assemble`, which proves the same.
        debug_assert!(s.is_ascii());
        unsafe { core::str::from_utf8_unchecked(s) }
    }

    /// The serialization of the URL, as bytes (always ASCII).
    pub fn as_bytes(&self) -> &[u8] {
        &self.href
    }

    /// The serialization of the URL (the URL Standard's `href`).
    pub fn href(&self) -> &str {
        self.s(0, self.href.len())
    }

    /// The scheme followed by ":".
    pub fn protocol(&self) -> &str {
        self.s(0, self.scheme_end + 1)
    }

    /// The scheme, lowercase and without the ":".
    pub fn scheme(&self) -> &str {
        self.s(0, self.scheme_end)
    }

    /// Whether the URL has an authority (a host, possibly empty).
    pub fn has_authority(&self) -> bool {
        self.host_kind.is_some()
    }

    /// The username, percent-encoded, or "" if there is none.
    pub fn username(&self) -> &str {
        if self.has_authority() {
            self.s(self.scheme_end + 3, self.username_end)
        } else {
            ""
        }
    }

    /// The password, percent-encoded, or "" if there is none.
    pub fn password(&self) -> &str {
        if self.has_authority() && self.username_end + 1 < self.host_start {
            self.s(self.username_end + 1, self.host_start - 1)
        } else {
            ""
        }
    }

    /// The host, serialized ("[...]" for IPv6), or "" if there is none.
    pub fn hostname(&self) -> &str {
        self.s(self.host_start, self.host_end)
    }

    /// The port, or `None` if there is none. A scheme's default port is never stored.
    pub fn port(&self) -> Option<u16> {
        self.port
    }

    /// The host and, if there is one, ":" and the port.
    pub fn host(&self) -> &str {
        let end = match self.port {
            Some(_) => self.path_start - if self.has_dot { 2 } else { 0 },
            None => self.host_end,
        };
        self.s(self.host_start, end)
    }

    fn path_end(&self) -> usize {
        match (self.query_start, self.fragment_start) {
            (Some(q), _) => q,
            (None, Some(f)) => f,
            (None, None) => self.href.len(),
        }
    }

    /// The path, percent-encoded (the URL Standard's `pathname`).
    pub fn pathname(&self) -> &str {
        self.s(self.path_start, self.path_end())
    }

    /// Whether the path is opaque (as in `mailto:x`), not a list of segments.
    pub fn has_opaque_path(&self) -> bool {
        self.opaque_path
    }

    /// "?" and the query, or "" when the query is null or empty.
    pub fn search(&self) -> &str {
        match self.query_start {
            Some(q) => {
                let end = self.fragment_start.unwrap_or(self.href.len());
                if end - q <= 1 {
                    ""
                } else {
                    self.s(q, end)
                }
            }
            None => "",
        }
    }

    /// The query without "?", or `None` when it is null.
    pub fn query(&self) -> Option<&str> {
        self.query_start.map(|q| {
            let end = self.fragment_start.unwrap_or(self.href.len());
            self.s(q + 1, end)
        })
    }

    /// "#" and the fragment, or "" when the fragment is null or empty.
    pub fn hash(&self) -> &str {
        match self.fragment_start {
            Some(f) if self.href.len() - f > 1 => self.s(f, self.href.len()),
            _ => "",
        }
    }

    /// The fragment without "#", or `None` when it is null.
    pub fn fragment(&self) -> Option<&str> {
        self.fragment_start.map(|f| self.s(f + 1, self.href.len()))
    }

    /// Whether the scheme is special (http, https, ws, wss, ftp or file).
    pub fn is_special(&self) -> bool {
        self.special
    }

    /// The ASCII serialization of the URL's origin ("null" for an opaque
    /// origin).
    pub fn origin(&self) -> String {
        match self.scheme() {
            "http" | "https" | "ws" | "wss" | "ftp" => {
                let mut o = String::with_capacity(self.path_start);
                o.push_str(self.protocol());
                o.push_str("//");
                o.push_str(self.host());
                o
            }
            "blob" => match Url::parse(self.pathname(), None) {
                Some(u) if u.scheme() == "http" || u.scheme() == "https" => u.origin(),
                _ => "null".to_string(),
            },
            _ => "null".to_string(),
        }
    }
}

impl core::fmt::Display for Url {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.href())
    }
}

impl core::fmt::Debug for Url {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Url({:?})", self.href())
    }
}
