//! Node.js bindings (Node-API): `URL` (the WHATWG URL class's getters,
//! setters and `canParse`) and `parseJSON` (the shape of `JSON.parse`
//! without a reviver). Parsing is vurl's and vjson's; this module only
//! converts types.
#![warn(missing_docs)]
use napi::bindgen_prelude::*;
use napi::{Env, JsValue, Unknown};
use napi_derive::napi;
use verilith_bind::verilith_json::{self, Type, Value};
use verilith_bind::verilith_url;

fn parse_with_base(input: &str, base: Option<&str>) -> Option<verilith_url::Url> {
    match base {
        Some(b) => verilith_url::Url::parse(input, Some(&verilith_url::Url::parse(b, None)?)),
        None => verilith_url::Url::parse(input, None),
    }
}

/// A URL parsed by the WHATWG URL Standard.
#[napi(js_name = "URL")]
pub struct Url {
    url: verilith_url::Url,
}

#[napi]
impl Url {
    /// Parses `input`, against `base` if given. Throws if it is not a valid URL.
    #[napi(constructor)]
    pub fn new(input: String, base: Option<String>) -> Result<Url> {
        parse_with_base(&input, base.as_deref())
            .map(|url| Url { url })
            .ok_or_else(|| Error::new(Status::InvalidArg, format!("Invalid URL: {input}")))
    }

    /// Whether `new URL(input, base)` would succeed.
    #[napi(js_name = "canParse")]
    pub fn can_parse(input: String, base: Option<String>) -> bool {
        parse_with_base(&input, base.as_deref()).is_some()
    }

    /// The href.
    #[napi(getter)]
    pub fn href(&self) -> &str {
        self.url.href()
    }
    /// Parses `v` as the new URL. Throws if it is not valid.
    #[napi(setter, js_name = "href")]
    pub fn set_href(&mut self, v: String) -> Result<()> {
        if self.url.set_href(&v) {
            Ok(())
        } else {
            Err(Error::new(Status::InvalidArg, format!("Invalid URL: {v}")))
        }
    }
    /// The origin, serialized.
    #[napi(getter)]
    pub fn origin(&self) -> String {
        self.url.origin()
    }
    /// The protocol.
    #[napi(getter)]
    pub fn protocol(&self) -> &str {
        self.url.protocol()
    }
    // The other setters fail silently, as the URL Standard's do.
    /// Sets the protocol, as the URL Standard's setter does.
    #[napi(setter, js_name = "protocol")]
    pub fn set_protocol(&mut self, v: String) {
        self.url.set_protocol(&v);
    }
    /// The username.
    #[napi(getter)]
    pub fn username(&self) -> &str {
        self.url.username()
    }
    /// Sets the username, as the URL Standard's setter does.
    #[napi(setter, js_name = "username")]
    pub fn set_username(&mut self, v: String) {
        self.url.set_username(&v);
    }
    /// The password.
    #[napi(getter)]
    pub fn password(&self) -> &str {
        self.url.password()
    }
    /// Sets the password, as the URL Standard's setter does.
    #[napi(setter, js_name = "password")]
    pub fn set_password(&mut self, v: String) {
        self.url.set_password(&v);
    }
    /// The host.
    #[napi(getter)]
    pub fn host(&self) -> &str {
        self.url.host()
    }
    /// Sets the host, as the URL Standard's setter does.
    #[napi(setter, js_name = "host")]
    pub fn set_host(&mut self, v: String) {
        self.url.set_host(&v);
    }
    /// The hostname.
    #[napi(getter)]
    pub fn hostname(&self) -> &str {
        self.url.hostname()
    }
    /// Sets the hostname, as the URL Standard's setter does.
    #[napi(setter, js_name = "hostname")]
    pub fn set_hostname(&mut self, v: String) {
        self.url.set_hostname(&v);
    }
    /// The port, or the empty string.
    #[napi(getter)]
    pub fn port(&self) -> String {
        self.url.port().map(|p| p.to_string()).unwrap_or_default()
    }
    /// Sets the port, as the URL Standard's setter does.
    #[napi(setter, js_name = "port")]
    pub fn set_port(&mut self, v: String) {
        self.url.set_port(&v);
    }
    /// The pathname.
    #[napi(getter)]
    pub fn pathname(&self) -> &str {
        self.url.pathname()
    }
    /// Sets the pathname, as the URL Standard's setter does.
    #[napi(setter, js_name = "pathname")]
    pub fn set_pathname(&mut self, v: String) {
        self.url.set_pathname(&v);
    }
    /// The search.
    #[napi(getter)]
    pub fn search(&self) -> &str {
        self.url.search()
    }
    /// Sets the search, as the URL Standard's setter does.
    #[napi(setter, js_name = "search")]
    pub fn set_search(&mut self, v: String) {
        self.url.set_search(&v);
    }
    /// The hash.
    #[napi(getter)]
    pub fn hash(&self) -> &str {
        self.url.hash()
    }
    /// Sets the hash, as the URL Standard's setter does.
    #[napi(setter, js_name = "hash")]
    pub fn set_hash(&mut self, v: String) {
        self.url.set_hash(&v);
    }
    /// The href.
    #[napi(js_name = "toString")]
    pub fn to_string(&self) -> &str {
        self.url.href()
    }
    /// The href.
    #[napi(js_name = "toJSON")]
    pub fn to_json(&self) -> &str {
        self.url.href()
    }
}

fn to_js<'env>(env: &'env Env, v: Value<'_>) -> Result<Unknown<'env>> {
    Ok(match v.kind() {
        Type::Null => Null.into_unknown(env)?,
        Type::Bool => v.as_bool().unwrap_or(false).into_unknown(env)?,
        Type::Number => env.create_double(v.as_f64().unwrap_or(0.0))?.to_unknown(),
        Type::String => env.create_string(v.as_str().unwrap_or_default())?.to_unknown(),
        Type::Array => {
            let mut a = env.create_array(v.len().unwrap_or(0) as u32)?;
            for (i, e) in v.elements().into_iter().flatten().enumerate() {
                a.set(i as u32, to_js(env, e)?)?;
            }
            a.to_unknown()
        }
        Type::Object => {
            let mut o = Object::new(env)?;
            for (k, e) in v.members().into_iter().flatten() {
                let name = k.as_str().unwrap_or_default();
                let val = to_js(env, e)?;
                if name == "__proto__" {
                    // Define it as an own property, as JSON.parse does;
                    // assigning would call the prototype setter.
                    o.define_properties(&[napi::Property::new().with_utf8_name(&name)?.with_value(&val)])?;
                } else {
                    o.set_property(env.create_string(&name)?, val)?;
                }
            }
            o.to_unknown()
        }
    })
}

/// Parses a JSON text (a string or a Buffer) with the verified parser.
/// Throws a SyntaxError on invalid JSON.
#[napi(js_name = "parseJSON")]
pub fn parse_json(env: &Env, text: Either<String, Buffer>) -> Result<Unknown<'_>> {
    let bytes: &[u8] = match &text {
        Either::A(s) => s.as_bytes(),
        Either::B(b) => b,
    };
    match verilith_json::parse(bytes) {
        Ok(doc) => to_js(env, doc.root()),
        Err(e) => {
            env.throw_syntax_error(&e.to_string(), None::<String>);
            Err(Error::new(Status::PendingException, e.to_string()))
        }
    }
}
