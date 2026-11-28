//! The HTTP side: routes requests to the pipeline and answers them through
//! verilith-server. Unverified glue (TRUST.md).
use crate::proxy::{self, Fail, Keys, Limits, Source};
use verilith_server::{Field, Request, Response};

/// What the server needs to answer image requests.
pub struct Proxy {
    pub keys: Keys,
    pub limits: Limits,
    /// `IMGPROXY_LOCAL_FILESYSTEM_ROOT`: where `local://` sources live.
    pub local_root: Option<std::fs::File>,
    /// Whether `http://` and `https://` sources are allowed.
    pub http_sources: bool,
    /// How `https://` sources are fetched (with the `tls` feature and a
    /// CA bundle); `None` refuses them.
    pub tls: Option<proxy::Tls>,
    /// `IMGPROXY_ALLOWED_SOURCES`: if not empty, a source URL must start with one of these.
    pub allowed: Vec<Vec<u8>>,
    /// `IMGPROXY_TTL`: the `Cache-Control` max-age, in seconds.
    pub ttl: u64,
}

impl Proxy {
    /// The PNG for a request, or why there is none.
    pub fn answer(&self, method: &[u8], path: &[u8], body: &[u8]) -> Result<(Vec<u8>, proxy::Format), Fail> {
        let p = proxy::parse(path)?;
        if !proxy::check(&self.keys, p.signature, p.signed) {
            return Err(Fail::Forbidden);
        }
        let data = match &p.source {
            Source::Upload => {
                if method != b"POST" && method != b"PUT" {
                    return Err(Fail::BadUrl("Uploads are POST requests"));
                }
                if body.len() > self.limits.max_src_bytes {
                    return Err(Fail::Unprocessable("Source image file is too big"));
                }
                std::borrow::Cow::Borrowed(body)
            }
            src => {
                if method != b"GET" && method != b"HEAD" {
                    return Err(Fail::BadUrl("Method not allowed"));
                }
                let url: Vec<u8> = match src {
                    Source::Local(p) => [b"local://".as_slice(), p].concat(),
                    Source::Http(u) => u.clone(),
                    Source::Upload => unreachable!(),
                };
                if !self.allowed.is_empty() && !self.allowed.iter().any(|a| url.starts_with(a)) {
                    return Err(Fail::NotFound);
                }
                std::borrow::Cow::Owned(match src {
                    Source::Local(p) => {
                        let root = self.local_root.as_ref().ok_or(Fail::NotFound)?;
                        proxy::read_local(root, p, self.limits.max_src_bytes)?
                    }
                    Source::Http(u) => {
                        if !self.http_sources {
                            return Err(Fail::NotFound);
                        }
                        proxy::fetch(u, &self.limits, self.tls.as_ref())?
                    }
                    Source::Upload => unreachable!(),
                })
            }
        };
        Ok((proxy::process(&data, &p.opts, &self.limits)?, p.opts.format))
    }

    /// Answers one request.
    pub fn handle(&self, req: &Request, res: &mut Response) {
        let path = req.path();
        if path == b"/health" {
            let _ = res.send(200, &[Field { name: b"Content-Type", value: b"text/plain" }], b"imgproxy is running");
            return;
        }
        match self.answer(req.method, path, req.body) {
            Ok((img, fmt)) => {
                let cc = format!("max-age={}, public", self.ttl);
                let _ = res.send(
                    200,
                    &[
                        Field { name: b"Content-Type", value: fmt.mime() },
                        Field { name: b"Cache-Control", value: cc.as_bytes() },
                    ],
                    &img,
                );
            }
            Err(e) => {
                let _ = res.send(
                    e.status(),
                    &[Field { name: b"Content-Type", value: b"text/plain" }, Field { name: b"Cache-Control", value: b"no-cache" }],
                    e.message().as_bytes(),
                );
            }
        }
    }
}
