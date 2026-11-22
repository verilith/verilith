//! Node.js bindings (Node-API): `URL` (the WHATWG URL class's getters,
//! setters and `canParse`) and `parseJSON` (the shape of `JSON.parse`
//! without a reviver). Parsing is vurl's and vjson's; this module only
//! converts types.
use napi::bindgen_prelude::*;
use napi::{Env, JsUnknown};
use napi_derive::napi;
use verilith_bind::verilith_json::{self, Type, Value};
use verilith_bind::vurl;

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
    #[napi(constructor)]
    pub fn new(input: String, base: Option<String>) -> Result<Url> {
        parse_with_base(&input, base.as_deref())
            .map(|url| Url { url })
            .ok_or_else(|| Error::new(Status::InvalidArg, format!("Invalid URL: {input}")))
    }

    #[napi(js_name = "canParse")]
    pub fn can_parse(input: String, base: Option<String>) -> bool {
        parse_with_base(&input, base.as_deref()).is_some()
    }

    #[napi(getter)]
    pub fn href(&self) -> &str {
        self.url.href()
    }
    #[napi(setter, js_name = "href")]
    pub fn set_href(&mut self, v: String) -> Result<()> {
        if self.url.set_href(&v) {
            Ok(())
        } else {
            Err(Error::new(Status::InvalidArg, format!("Invalid URL: {v}")))
        }
    }
    #[napi(getter)]
    pub fn origin(&self) -> String {
        self.url.origin()
    }
    #[napi(getter)]
    pub fn protocol(&self) -> &str {
        self.url.protocol()
    }
    // The other setters fail silently, as the URL Standard's do.
    #[napi(setter, js_name = "protocol")]
    pub fn set_protocol(&mut self, v: String) {
        self.url.set_protocol(&v);
    }
    #[napi(getter)]
    pub fn username(&self) -> &str {
        self.url.username()
    }
    #[napi(setter, js_name = "username")]
    pub fn set_username(&mut self, v: String) {
        self.url.set_username(&v);
    }
    #[napi(getter)]
    pub fn password(&self) -> &str {
        self.url.password()
    }
    #[napi(setter, js_name = "password")]
    pub fn set_password(&mut self, v: String) {
        self.url.set_password(&v);
    }
    #[napi(getter)]
    pub fn host(&self) -> &str {
        self.url.host()
    }
    #[napi(setter, js_name = "host")]
    pub fn set_host(&mut self, v: String) {
        self.url.set_host(&v);
    }
    #[napi(getter)]
    pub fn hostname(&self) -> &str {
        self.url.hostname()
    }
    #[napi(setter, js_name = "hostname")]
    pub fn set_hostname(&mut self, v: String) {
        self.url.set_hostname(&v);
    }
    #[napi(getter)]
    pub fn port(&self) -> String {
        self.url.port().map(|p| p.to_string()).unwrap_or_default()
    }
    #[napi(setter, js_name = "port")]
    pub fn set_port(&mut self, v: String) {
        self.url.set_port(&v);
    }
    #[napi(getter)]
    pub fn pathname(&self) -> &str {
        self.url.pathname()
    }
    #[napi(setter, js_name = "pathname")]
    pub fn set_pathname(&mut self, v: String) {
        self.url.set_pathname(&v);
    }
    #[napi(getter)]
    pub fn search(&self) -> &str {
        self.url.search()
    }
    #[napi(setter, js_name = "search")]
    pub fn set_search(&mut self, v: String) {
        self.url.set_search(&v);
    }
    #[napi(getter)]
    pub fn hash(&self) -> &str {
        self.url.hash()
    }
    #[napi(setter, js_name = "hash")]
    pub fn set_hash(&mut self, v: String) {
        self.url.set_hash(&v);
    }
    #[napi(js_name = "toString")]
    pub fn to_string(&self) -> &str {
        self.url.href()
    }
    #[napi(js_name = "toJSON")]
    pub fn to_json(&self) -> &str {
        self.url.href()
    }
}

fn to_js(env: &Env, v: Value<'_>) -> Result<JsUnknown> {
    Ok(match v.kind() {
        Type::Null => env.get_null()?.into_unknown(),
        Type::Bool => env.get_boolean(v.as_bool().unwrap_or(false))?.into_unknown(),
        Type::Number => env.create_double(v.as_f64().unwrap_or(0.0))?.into_unknown(),
        Type::String => env.create_string(&v.as_str().unwrap_or_default())?.into_unknown(),
        Type::Array => {
            let mut a = env.create_array_with_length(v.len().unwrap_or(0))?;
            for (i, e) in v.elements().into_iter().flatten().enumerate() {
                a.set_element(i as u32, to_js(env, e)?)?;
            }
            a.into_unknown()
        }
        Type::Object => {
            let mut o = env.create_object()?;
            for (k, e) in v.members().into_iter().flatten() {
                let name = k.as_str().unwrap_or_default();
                let val = to_js(env, e)?;
                if name == "__proto__" {
                    // Define it as an own property, as JSON.parse does;
                    // assigning would call the prototype setter.
                    o.define_properties(&[napi::Property::new(&name)?.with_value(&val)])?;
                } else {
                    o.set_property(env.create_string(&name)?, val)?;
                }
            }
            o.into_unknown()
        }
    })
}

/// Parses a JSON text (a string or a Buffer) with the verified parser.
/// Throws a SyntaxError on invalid JSON.
#[napi(js_name = "parseJSON")]
pub fn parse_json(env: Env, text: Either<String, Buffer>) -> Result<JsUnknown> {
    let bytes: &[u8] = match &text {
        Either::A(s) => s.as_bytes(),
        Either::B(b) => b,
    };
    match verilith_json::parse(bytes) {
        Ok(doc) => to_js(&env, doc.root()),
        Err(e) => {
            env.throw_syntax_error(&e.to_string(), None::<String>);
            Err(Error::new(Status::PendingException, e.to_string()))
        }
    }
}
