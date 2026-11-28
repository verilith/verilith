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

/// A successful answer.
#[derive(Debug, PartialEq, Eq)]
pub struct Answer {
    pub body: Vec<u8>,
    pub mime: &'static [u8],
    pub disposition: Vec<u8>,
}

impl Proxy {
    /// The image for a request, or why there is none.
    pub fn answer(&self, method: &[u8], path: &[u8], body: &[u8]) -> Result<Answer, Fail> {
        let p = proxy::parse(path)?;
        if !proxy::check(&self.keys, p.signature, p.signed) {
            return Err(Fail::Forbidden);
        }
        if p.opts.expires != 0 {
            let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs());
            if now > p.opts.expires {
                return Err(Fail::Expired);
            }
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
        let fname = p.filename.as_deref();
        // `raw` and `skip_processing`: the source as it is, with its own type.
        let k = crate::url::kind_x(&data);
        if p.opts.raw || k.is_some_and(|k| p.opts.skip & k.bit() != 0) {
            let disposition = proxy::disposition(fname, &p.source, p.opts.attachment, k);
            let mime = k.map_or(&b"application/octet-stream"[..], |k| k.mime());
            return Ok(Answer { body: data.into_owned(), mime, disposition });
        }
        let out = proxy::process(&data, &p.opts, &self.limits)?;
        let k = p.opts.format.kind();
        Ok(Answer { body: out, mime: k.mime(), disposition: proxy::disposition(fname, &p.source, p.opts.attachment, Some(k)) })
    }

    /// Answers one request.
    pub fn handle(&self, req: &Request, res: &mut Response) {
        let path = req.path();
        if path == b"/health" {
            let _ = res.send(200, &[Field { name: b"Content-Type", value: b"text/plain" }], b"imgproxy is running");
            return;
        }
        match self.answer(req.method, path, req.body) {
            Ok(a) => {
                let cc = format!("max-age={}, public", self.ttl);
                let _ = res.send(
                    200,
                    &[
                        Field { name: b"Content-Type", value: a.mime },
                        Field { name: b"Cache-Control", value: cc.as_bytes() },
                        Field { name: b"Content-Disposition", value: &a.disposition },
                    ],
                    &a.body,
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
