// Bun baseline for bench/server: Bun.serve (uWebSockets underneath).
// One process per worker, all on the same ports with reusePort, which is
// how Bun scales across cores.
//   bun server.js HTTP_PORT TLS_PORT CERT KEY ROOT
const [http, tls, cert, key, root] = process.argv.slice(2);
const files = {};
for (const name of ["1k.bin", "64k.bin", "1m.bin"]) {
  files["/static/" + name] = Bun.file(root + "/" + name);
}
const plain = { "Content-Type": "text/plain", "Server": "bun" };
const octet = { "Content-Type": "application/octet-stream", "Server": "bun" };
function fetch(req) {
  const path = new URL(req.url).pathname;
  if (path === "/plaintext") return new Response("Hello, World!", { headers: plain });
  const f = files[path];
  if (f) return new Response(f, { headers: octet });
  return new Response("not found", { status: 404, headers: plain });
}
Bun.serve({ port: +http, hostname: "127.0.0.1", reusePort: true, fetch });
Bun.serve({ port: +tls, hostname: "127.0.0.1", reusePort: true, fetch,
  tls: { cert: Bun.file(cert), key: Bun.file(key) } });
