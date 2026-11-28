#![doc = include_str!("../README.md")]
// A formally verified serverless host: untrusted WebAssembly request
// handlers, run by verilith-wasm behind verilith-server.
//
// - [`abi`]: the guest ABI, its specification and the verified host.
// - [`host`]: per-request isolation, limits and routing (verified).
// - the rest of this file: loading modules and the server handler, plain
//   Rust (TRUST.md).
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables, unused_imports, dead_code, non_shorthand_field_patterns))]
pub mod abi;
pub mod host;

#[cfg(not(verus_keep_ghost))]
pub use glue::*;

#[cfg(not(verus_keep_ghost))]
mod glue {
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::sync::Arc;

    use verilith_server::{Field, Request, Response};
    use verilith_wasm::ast::{ImportDesc, Trap, ValType};
    use verilith_wasm::{Instance, Linker, Module};

    use crate::abi::{arity_of, op_of, Limits, Req};
    use crate::host::{route, Func, Outcome};

    /// The import module every ABI function lives in.
    pub const ABI_MODULE: &str = "vl";
    /// The export each request calls: `() -> ()`.
    pub const ENTRY: &str = "handle";

    /// Per-function limits.
    #[derive(Clone, Copy, Debug)]
    pub struct Options {
        /// Fuel per request (each branch, call and return costs one).
        pub fuel: u64,
        /// Linear memory cap per instance, in bytes (whole 64 KiB pages).
        pub max_memory: u64,
        /// Largest response body.
        pub max_body: usize,
        /// Most response fields.
        pub max_fields: usize,
        /// Most bytes of response field names and values together.
        pub max_field_bytes: usize,
    }

    impl Default for Options {
        fn default() -> Self {
            Options {
                fuel: 100_000_000,
                max_memory: 64 << 20,
                max_body: 8 << 20,
                max_fields: 64,
                max_field_bytes: 16 << 10,
            }
        }
    }

    impl Options {
        fn limits(&self) -> Limits {
            Limits { max_body: self.max_body, max_fields: self.max_fields, max_field_bytes: self.max_field_bytes }
        }
    }

    /// Why a module could not be loaded.
    #[derive(Debug)]
    pub enum LoadError {
        /// verilith-wasm refused it (decoding, validation, linking, instantiation).
        Wasm(verilith_wasm::Error),
        /// An import that is not an ABI function, or one with the wrong type.
        Import(String),
        /// No `handle: () -> ()` export.
        NoEntry,
        /// The memory's limit is above the cap.
        Memory,
    }

    impl std::fmt::Display for LoadError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self:?}")
        }
    }

    impl std::error::Error for LoadError {}

    /// Decodes, validates and instantiates `wasm` (running its start
    /// function, which may not call the ABI), and prepares it to serve
    /// requests.
    pub fn load(wasm: &[u8], opts: &Options) -> Result<Func, LoadError> {
        let module = Module::new(wasm).map_err(LoadError::Wasm)?;
        let mut ops = Vec::new();
        let mut linker = Linker::new();
        for imp in module.imports() {
            let what = || format!("{}.{}", String::from_utf8_lossy(&imp.module), String::from_utf8_lossy(&imp.name));
            if imp.module != ABI_MODULE.as_bytes() {
                return Err(LoadError::Import(what()));
            }
            let ImportDesc::Func(_) = imp.desc else { return Err(LoadError::Import(what())) };
            // The verified `op_of` names the ABI function, so import `i` is
            // the one its name says (`ops[i]`).
            let Some(op) = op_of(&imp.name) else { return Err(LoadError::Import(what())) };
            let Ok(name) = std::str::from_utf8(&imp.name) else { return Err(LoadError::Import(what())) };
            ops.push(op);
            // Only the start function can reach these: the ABI is not
            // available while instantiating.
            linker.func(ABI_MODULE, name, &vec![ValType::I32; arity_of(op)], &[ValType::I32], |_, _, _| Err(Trap::Host));
        }
        linker.fuel(opts.fuel);
        linker.max_memory(opts.max_memory);
        let inst = Instance::new(module, &linker).map_err(LoadError::Wasm)?;
        let entry = match inst.export_func(ENTRY) {
            Some((x, p, r)) if p.is_empty() && r.is_empty() => x,
            _ => return Err(LoadError::NoEntry),
        };
        let checked = inst.into_checked().ok_or(LoadError::NoEntry)?;
        let cap = (opts.max_memory / 65536).min(65536) as u32;
        Func::new(checked, ops, entry, opts.fuel, cap).ok_or(LoadError::Memory)
    }

    /// The request's header lines, `name: value\r\n` each.
    fn field_lines(req: &Request, out: &mut Vec<u8>) {
        out.clear();
        for (n, v) in req.headers() {
            out.extend_from_slice(n);
            out.extend_from_slice(b": ");
            out.extend_from_slice(v);
            out.extend_from_slice(b"\r\n");
        }
    }

    /// Runs one request on `f` and writes the response.
    pub fn respond(f: Func, req: &Request, res: &mut Response, lim: Limits, scratch: &mut Vec<u8>) -> Func {
        field_lines(req, scratch);
        let q = Req { method: req.method, target: req.target, fields: scratch, body: req.body };
        let (f, out, _) = f.serve(q, lim);
        match out {
            Outcome::Done(rep) => {
                let n = rep.n_fields();
                let mut fields = Vec::with_capacity(n);
                for i in 0..n {
                    let (name, value) = rep.field(i);
                    fields.push(Field { name, value });
                }
                // Every field passes the server's checks (`reply_ok`), so
                // this cannot fail for the reply's sake.
                if res.send(rep.status(), &fields, rep.body()).is_err() {
                    res.error(500);
                }
            }
            Outcome::Trap(Trap::Exhausted) => {
                let _ = res.send(503, &[], b"function ran out of fuel or stack\n");
            }
            Outcome::Trap(_) => {
                let _ = res.send(500, &[], b"function trapped\n");
            }
            Outcome::Fault => res.error(500),
        }
        f
    }

    struct Entry {
        wasm: Arc<[u8]>,
        opts: Options,
    }

    /// Functions by name, served at `/fn/<name>` (and below it). A
    /// [`verilith_server::Handler`]: each worker thread instantiates a
    /// function the first time it serves it, and keeps that instance.
    pub struct Functions {
        fns: HashMap<Vec<u8>, Entry>,
        id: usize,
    }

    struct Local {
        id: usize,
        fns: HashMap<Vec<u8>, Option<Func>>,
        scratch: Vec<u8>,
    }

    thread_local! {
        static LOCAL: RefCell<Vec<Local>> = const { RefCell::new(Vec::new()) };
    }

    static NEXT_ID: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

    impl Default for Functions {
        fn default() -> Self {
            Functions::new()
        }
    }

    impl Functions {
        pub fn new() -> Functions {
            Functions { fns: HashMap::new(), id: NEXT_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed) }
        }

        /// Adds function `name` (`[a-z0-9_-]{1,64}`). Loads it once here, so
        /// a bad module is refused now rather than on the first request.
        pub fn add(&mut self, name: &str, wasm: &[u8], opts: Options) -> Result<(), LoadError> {
            let ok = !name.is_empty()
                && name.len() <= crate::host::MAX_NAME
                && name.bytes().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'-' || c == b'_');
            if !ok {
                return Err(LoadError::Import(format!("bad function name {name:?}")));
            }
            load(wasm, &opts)?;
            self.fns.insert(name.as_bytes().to_vec(), Entry { wasm: wasm.into(), opts });
            Ok(())
        }

        /// Serves `req` if its path names a function; `false` otherwise.
        pub fn serve(&self, req: &Request, res: &mut Response) -> bool {
            let path = req.path();
            let Some(e) = route(path) else { return false };
            let name = &path[4..e];
            let Some(entry) = self.fns.get(name) else {
                res.error(404);
                return true;
            };
            LOCAL.with(|l| {
                let mut l = l.borrow_mut();
                let i = match l.iter().position(|x| x.id == self.id) {
                    Some(i) => i,
                    None => {
                        l.push(Local { id: self.id, fns: HashMap::new(), scratch: Vec::new() });
                        l.len() - 1
                    }
                };
                let local = &mut l[i];
                // The name is copied only the first time this thread serves it.
                let f = match local.fns.get_mut(name).and_then(Option::take) {
                    Some(f) => f,
                    None => match load(&entry.wasm, &entry.opts) {
                        Ok(f) => f,
                        Err(_) => {
                            res.error(500);
                            return;
                        }
                    },
                };
                let f = respond(f, req, res, entry.opts.limits(), &mut local.scratch);
                match local.fns.get_mut(name) {
                    Some(slot) => *slot = Some(f),
                    None => {
                        local.fns.insert(name.to_vec(), Some(f));
                    }
                }
            });
            true
        }
    }

    impl verilith_server::Handler for Functions {
        fn handle(&self, req: &Request, res: &mut Response) {
            if !self.serve(req, res) {
                res.error(404);
            }
        }
    }
}
