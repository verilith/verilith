//! The URL Standard's API setters (href, protocol, username, password, host,
//! hostname, port, pathname, search, hash).
//!
//! Each setter is proven in `set.rs` to leave the URL that the Standard's
//! setter leaves (`spec::set_protocol`, ... `spec::set_hash`, which run the
//! basic URL parser with a state override). This file only adapts them to
//! `&mut self` and to the boolean results that ada's API reports, which the
//! Standard does not define.
use crate::set::*;
use crate::url::Url;

impl Url {
    /// The href setter: parses `value` and replaces this URL. Returns false
    /// (and leaves the URL unchanged) if it does not parse.
    pub fn set_href(&mut self, value: &str) -> bool {
        match Url::parse(value, None) {
            Some(u) => {
                *self = u;
                true
            }
            None => false,
        }
    }

    /// The protocol setter. True if the scheme changed, or the value was
    /// empty once tab and newline are removed.
    pub fn set_protocol(&mut self, value: &str) -> bool {
        match set_protocol_bytes(self, value.as_bytes()) {
            Some(u) => {
                *self = u;
                true
            }
            None => value.bytes().all(|c| c == b'\t' || c == b'\n' || c == b'\r'),
        }
    }

    /// The username setter. False if this URL cannot have a username.
    pub fn set_username(&mut self, value: &str) -> bool {
        self.replace(set_credential(self, value.as_bytes(), false))
    }

    /// The password setter. False if this URL cannot have a password.
    pub fn set_password(&mut self, value: &str) -> bool {
        self.replace(set_credential(self, value.as_bytes(), true))
    }

    fn replace(&mut self, u: Option<Url>) -> bool {
        match u {
            Some(u) => {
                *self = u;
                true
            }
            None => false,
        }
    }

    fn replace_with(&mut self, r: (Option<Url>, bool)) -> bool {
        if let Some(u) = r.0 {
            *self = u;
        }
        r.1
    }

    /// The host setter. False if the host was rejected.
    pub fn set_host(&mut self, value: &str) -> bool {
        let r = set_host_bytes(self, value.as_bytes(), false);
        self.replace_with(r)
    }

    /// The hostname setter. False if the hostname was rejected.
    pub fn set_hostname(&mut self, value: &str) -> bool {
        let r = set_host_bytes(self, value.as_bytes(), true);
        self.replace_with(r)
    }

    /// `set_hostname` on a copy: the setter's result, and the edited URL
    /// when it differs from `self` (`None` means it is `self`).
    pub fn with_hostname(&self, value: &str) -> (bool, Option<Url>) {
        let (u, ok) = set_host_bytes(self, value.as_bytes(), true);
        (ok, u)
    }

    /// The host that `set_hostname` would give this URL, without making the
    /// new URL: `None` when this shortcut does not apply (call
    /// `with_hostname`), `Some(None)` when the setter fails, and otherwise
    /// the new host's kind, its serialization being left in `out`.
    pub fn hostname_host(&self, value: &str, out: &mut Vec<u8>) -> Option<Option<crate::host::HostKind>> {
        self.hostname_host_in(value, out, &mut crate::host::Scratch::new())
    }

    /// `hostname_host` with the host parser's scratch storage kept by the
    /// caller.
    pub(crate) fn hostname_host_in(&self, value: &str, out: &mut Vec<u8>, sc: &mut crate::host::Scratch) -> Option<Option<crate::host::HostKind>> {
        out.clear();
        hostname_host(self, value.as_bytes(), out, sc).map(|(k, _)| k)
    }

    /// The port setter. False if the port was rejected.
    pub fn set_port(&mut self, value: &str) -> bool {
        let r = set_port_bytes(self, value.as_bytes());
        self.replace_with(r)
    }

    /// The pathname setter. False if this URL has an opaque path.
    pub fn set_pathname(&mut self, value: &str) -> bool {
        self.replace(set_pathname_bytes(self, value.as_bytes()))
    }

    pub fn set_search(&mut self, value: &str) {
        *self = set_search_bytes(self, value.as_bytes());
    }

    pub fn set_hash(&mut self, value: &str) {
        *self = set_hash_bytes(self, value.as_bytes());
    }
}
