//! Python bindings: `vbind.URL` (the shape of the `ada_url` package's `URL`)
//! and `vbind.loads` (the shape of `json.loads`). Parsing is vurl's and
//! vjson's; this module only converts types.
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList, PyString};
use verilith_bind::verilith_json::{self, Type, Value};
use verilith_bind::vurl;

/// A URL parsed by the WHATWG URL Standard.
#[pyclass(module = "vbind")]
#[derive(Clone)]
struct URL {
    url: verilith_url::Url,
}

fn parse_with_base(input: &str, base: Option<&str>) -> Option<verilith_url::Url> {
    match base {
        Some(b) => verilith_url::Url::parse(input, Some(&verilith_url::Url::parse(b, None)?)),
        None => verilith_url::Url::parse(input, None),
    }
}

fn setter(ok: bool, what: &str, value: &str) -> PyResult<()> {
    if ok {
        Ok(())
    } else {
        Err(PyValueError::new_err(format!("invalid {what}: {value:?}")))
    }
}

#[pymethods]
impl URL {
    #[new]
    #[pyo3(signature = (url, base = None))]
    fn new(url: &str, base: Option<&str>) -> PyResult<URL> {
        parse_with_base(url, base)
            .map(|url| URL { url })
            .ok_or_else(|| PyValueError::new_err(format!("invalid URL: {url:?}")))
    }

    /// Whether `url` parses (against `base`, if given).
    #[staticmethod]
    #[pyo3(signature = (url, base = None))]
    fn can_parse(url: &str, base: Option<&str>) -> bool {
        parse_with_base(url, base).is_some()
    }

    #[getter]
    fn href(&self) -> &str {
        self.url.href()
    }
    #[setter]
    fn set_href(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_href(v), "href", v)
    }
    #[getter]
    fn origin(&self) -> String {
        self.url.origin()
    }
    #[getter]
    fn protocol(&self) -> &str {
        self.url.protocol()
    }
    #[setter]
    fn set_protocol(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_protocol(v), "protocol", v)
    }
    #[getter]
    fn username(&self) -> &str {
        self.url.username()
    }
    #[setter]
    fn set_username(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_username(v), "username", v)
    }
    #[getter]
    fn password(&self) -> &str {
        self.url.password()
    }
    #[setter]
    fn set_password(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_password(v), "password", v)
    }
    #[getter]
    fn host(&self) -> &str {
        self.url.host()
    }
    #[setter]
    fn set_host(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_host(v), "host", v)
    }
    #[getter]
    fn hostname(&self) -> &str {
        self.url.hostname()
    }
    #[setter]
    fn set_hostname(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_hostname(v), "hostname", v)
    }
    #[getter]
    fn port(&self) -> String {
        self.url.port().map(|p| p.to_string()).unwrap_or_default()
    }
    #[setter]
    fn set_port(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_port(v), "port", v)
    }
    #[getter]
    fn pathname(&self) -> &str {
        self.url.pathname()
    }
    #[setter]
    fn set_pathname(&mut self, v: &str) -> PyResult<()> {
        setter(self.url.set_pathname(v), "pathname", v)
    }
    #[getter]
    fn search(&self) -> &str {
        self.url.search()
    }
    #[setter]
    fn set_search(&mut self, v: &str) {
        self.url.set_search(v)
    }
    #[getter]
    fn hash(&self) -> &str {
        self.url.hash()
    }
    #[setter]
    fn set_hash(&mut self, v: &str) {
        self.url.set_hash(v)
    }

    fn __str__(&self) -> &str {
        self.url.href()
    }
    fn __repr__(&self) -> String {
        format!("<URL {:?}>", self.url.href())
    }
    fn __eq__(&self, other: &URL) -> bool {
        self.url.href() == other.url.href()
    }
    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.url.href().hash(&mut h);
        h.finish()
    }
}

fn to_py(py: Python<'_>, v: Value<'_>) -> PyResult<PyObject> {
    Ok(match v.kind() {
        Type::Null => py.None(),
        Type::Bool => v.as_bool().unwrap_or(false).into_pyobject(py)?.to_owned().into_any().unbind(),
        Type::Number => {
            let lex = v.as_number_str().unwrap_or("0");
            if let Some(i) = v.as_i64() {
                i.into_pyobject(py)?.into_any().unbind()
            } else if lex.bytes().any(|c| matches!(c, b'.' | b'e' | b'E')) {
                v.as_f64().unwrap_or(0.0).into_pyobject(py)?.into_any().unbind()
            } else {
                // An integer beyond i64: Python's int is unbounded, as in json.loads.
                py.get_type::<pyo3::types::PyInt>().call1((lex,))?.unbind()
            }
        }
        Type::String => PyString::new(py, &v.as_str().unwrap_or_default()).into_any().unbind(),
        Type::Array => {
            let l = PyList::empty(py);
            for e in v.elements().into_iter().flatten() {
                l.append(to_py(py, e)?)?;
            }
            l.into_any().unbind()
        }
        Type::Object => {
            let d = PyDict::new(py);
            for (k, e) in v.members().into_iter().flatten() {
                d.set_item(PyString::new(py, &k.as_str().unwrap_or_default()), to_py(py, e)?)?;
            }
            d.into_any().unbind()
        }
    })
}

/// Parses a JSON text (str, bytes or bytearray) into Python objects, as
/// `json.loads` does. Raises ValueError on invalid JSON.
#[pyfunction]
fn loads(py: Python<'_>, s: &Bound<'_, PyAny>) -> PyResult<PyObject> {
    let text;
    let owned;
    let bytes: &[u8] = if let Ok(st) = s.downcast::<PyString>() {
        text = st.to_cow()?;
        text.as_bytes()
    } else if let Ok(b) = s.downcast::<PyBytes>() {
        b.as_bytes()
    } else {
        owned = s.extract::<Vec<u8>>()?;
        &owned
    };
    match verilith_json::parse(bytes) {
        Ok(doc) => to_py(py, doc.root()),
        Err(e) => Err(PyValueError::new_err(e.to_string())),
    }
}

#[pymodule]
#[pyo3(name = "vbind")]
fn vbind_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<URL>()?;
    m.add_function(wrap_pyfunction!(loads, m)?)?;
    Ok(())
}
