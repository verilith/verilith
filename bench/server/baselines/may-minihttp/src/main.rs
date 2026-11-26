//! may-minihttp baseline for bench/server.
//!   may-minihttp-hello --threads N --http PORT --root DIR
use std::collections::HashMap;
use std::io;
use std::sync::Arc;

use may_minihttp::{HttpService, HttpServiceFactory, Request, Response};

#[derive(Clone)]
struct Svc {
    files: Arc<HashMap<String, &'static [u8]>>,
}

impl HttpService for Svc {
    fn call(&mut self, req: Request, res: &mut Response) -> io::Result<()> {
        let path = req.path();
        if path == "/plaintext" {
            res.header("Content-Type: text/plain");
            res.body("Hello, World!");
        } else if let Some(b) = self.files.get(path) {
            res.header("Content-Type: application/octet-stream");
            res.body_vec(b.to_vec());
        } else {
            res.status_code(404, "Not Found");
            res.body("not found");
        }
        Ok(())
    }
}

struct Factory(Svc);

impl HttpServiceFactory for Factory {
    type Service = Svc;
    fn new_service(&self, _: usize) -> Svc {
        self.0.clone()
    }
}

fn arg(args: &[String], k: &str) -> Option<String> {
    args.iter().position(|a| a == k).map(|i| args[i + 1].clone())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let threads: usize = arg(&args, "--threads").map_or(1, |s| s.parse().unwrap());
    let port = arg(&args, "--http").unwrap();
    let root = arg(&args, "--root").unwrap();
    let mut files = HashMap::new();
    for e in std::fs::read_dir(&root).unwrap() {
        let e = e.unwrap();
        if e.file_type().unwrap().is_file() {
            let b: &'static [u8] = Box::leak(std::fs::read(e.path()).unwrap().into_boxed_slice());
            files.insert(format!("/static/{}", e.file_name().into_string().unwrap()), b);
        }
    }
    may::config().set_workers(threads).set_stack_size(0x1000);
    let s = Factory(Svc { files: Arc::new(files) });
    let h = s.start(format!("127.0.0.1:{port}")).unwrap();
    h.join().unwrap();
}
