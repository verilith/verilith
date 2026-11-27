# The cryptography verilith-tls trusts, primitive by primitive

verilith-tls proves its handshake, key schedule and record layer, and takes
the primitives below on trust through the `Provider` trait
(`crates/tls/src/crypto.rs`). This file lists every one this crate calls,
what formal proof stands behind the code that actually runs, and which
implementation we use. The rule: where aws-lc's code is unproven and a
verified implementation is about as fast, use the verified one; otherwise
keep aws-lc and say so here.

aws-lc is aws-lc-sys 0.47.0 (aws-lc-rs 1.19). Its proofs are in
[aws-lc-verification](https://github.com/awslabs/aws-lc-verification)
(SAW, for a few algorithms on some x86-64 and Neoverse CPUs),
[s2n-bignum](https://github.com/awslabs/s2n-bignum) (HOL Light, x86-64 and
AArch64 assembly for curve and bignum arithmetic) and
[mlkem-native](https://github.com/pq-code-package/mlkem-native) (ML-KEM).
The alternatives are [libcrux](https://github.com/cryspen/libcrux)'s crates
built from [HACL*](https://github.com/hacl-star/hacl-star) (F*: memory
safety, functional correctness, secret independence) and this repository's
own verilith-sha2 (Verus).

## Inventory

| Primitive | Used for | Implementation | Proof behind the code that runs |
|---|---|---|---|
| SHA-256, SHA-384, HMAC, HKDF | Transcript hash, key schedule, Finished, binders | verilith-sha2 (in verilith-tls itself) | Verus, this repository |
| HMAC-SHA-256 | HPKE key schedule for ECH (`hpke.rs`) | **verilith-sha2** (was aws-lc) | Verus, this repository. aws-lc's HMAC proof is for SHA-384 only |
| ChaCha20-Poly1305 | Session tickets (`TicketKeys`) | **libcrux** (was aws-lc) | HACL* |
| ChaCha20-Poly1305 | HPKE suite 0x0003, ECH | **libcrux** (was aws-lc) | HACL* |
| ChaCha20-Poly1305 | TLS records, QUIC packets | aws-lc | None: OpenSSL-derived assembly |
| AES-128-GCM, AES-256-GCM | TLS records, QUIC packets, HPKE suites 0x0001 and 0x0002 | **verilith-aes** (was aws-lc); aws-lc on a CPU without AES and carry-less multiply instructions | Verus, this repository: GCM-AE and GCM-AD of SP 800-38D with additional data, every length, both key sizes, for the kernels that run: x86-64 AES-NI and PCLMULQDQ, the 16-block VAES and VPCLMULQDQ kernel on AVX-512 CPUs, and AArch64 FEAT_AES and FEAT_PMULL. aws-lc's SAW proof covers AES-256-GCM only, on x86-64 Sandy Bridge to Skylake without AVX-512, for whole blocks, with additional data not verified |
| AES (raw) | QUIC header protection, AES suites | **verilith-aes** (was aws-lc), with the same fallback | Verus, this repository (FIPS 197 Cipher) |
| ChaCha20 (raw) | QUIC header protection, ChaCha20-Poly1305 suite | aws-lc | None |
| X25519 | Key share, the X25519 half of X25519MLKEM768, HPKE's DHKEM | aws-lc | s2n-bignum (`curve25519_x25519`, HOL Light) on x86-64 and AArch64 Linux and macOS; the C around it (clamping, the all-zero check) is not proven |
| ML-KEM-768 | X25519MLKEM768 | aws-lc (mlkem-native) | Partly: CBMC proves memory and type safety of the C, HOL Light proves the AArch64 and x86-64 assembly (NTT and friends) correct. The C is not proven functionally correct |
| P-256 ECDH | secp256r1 key share | aws-lc | Partly: s2n-bignum's scalar multiplication (`p256_montjscalarmul`) and inversion; the field arithmetic and base-point multiplication are OpenSSL's nistz256 assembly, unproven |
| ECDSA P-256 | Server signature, client certificate and CertificateVerify checks | aws-lc | Partly, as P-256 ECDH. The ECDSA layer is not proven |
| P-384 ECDH, ECDSA P-384 | secp384r1 key share, signatures | aws-lc | Partly: s2n-bignum field arithmetic; the earlier SAW proofs of ECDSA and ECDH P-384 are no longer listed as maintained |
| Ed25519 | Server signature, client certificate checks | aws-lc | Partly: s2n-bignum's Edwards25519 scalar multiplications (HOL Light); SHA-512, encoding and the rest of the C are not proven |
| RSA-PSS sign, RSA PKCS #1 v1.5 and PSS verify | Server signature, certificate checks | aws-lc | Partly: s2n-bignum Montgomery arithmetic on some paths; the padding and the rest of RSA are not proven |
| Random numbers | Key shares, nonces, ticket keys | aws-lc's DRBG over the OS | Not provable; trusted |

The rustls and quinn-proto backends that verilith-server keeps for
comparison (`--tls-backend rustls`, `--h3-backend quinn`) also run on aws-lc
and are outside this list: they are off unless chosen.

## What was swapped, and why the rest was not

Each line is aws-lc against the verified alternative, measured with
`bench/` (`cargo run --release` there): best of 7 runs of 200 ms on a cloud
x86-64 (Xeon, 2.1 GHz, AVX-512, VAES), 2026-11-27. The AES-GCM rows are
from a later run on the same kind of machine (2.3 GHz), the same day.

| Operation | aws-lc | Verified alternative | Ratio | Decision |
|---|---:|---:|---:|---|
| HMAC-SHA-256, 100 B | 0.44 us | 0.28 us (verilith-sha2) | 0.6x | Swapped (HPKE) |
| AES-128-GCM seal, 16 KiB (TLS record) | 0.98 us, 16.7 GB/s | 1.21 us, 13.6 GB/s (verilith-aes) | 1.23x | Swapped: about 0.2 us more per full record, against an unproven kernel replaced by a proven one. aws-lc's lead is its stitched AVX-512 assembly |
| AES-128-GCM open, 16 KiB (with a copy) | 1.14 us, 14.4 GB/s | 1.30 us, 12.6 GB/s | 1.14x | Swapped |
| AES-128-GCM seal, 1200 B (QUIC packet) | 0.193 us | 0.188 us | 0.97x | Swapped |
| AES-128-GCM open, 1200 B (with a copy) | 0.229 us | 0.192 us | 0.84x | Swapped |
| AES-128-GCM seal, 256 B | 0.139 us | 0.074 us | 0.53x | Swapped |
| AES-128-GCM seal, 64 B | 0.123 us | 0.080 us | 0.65x | Swapped |
| AES-256-GCM seal, 16 KiB | 1.18 us, 13.9 GB/s | 1.34 us, 12.2 GB/s | 1.14x | Swapped |
| AES-256-GCM seal, 1200 B | 0.214 us | 0.207 us | 0.97x | Swapped |
| AES-128 header protection mask | 0.036 us | 0.034 us | 0.94x | Swapped |
| ChaCha20-Poly1305 seal, 256 B | 0.32 us | 0.77 us (libcrux) | 2.4x | Swapped for tickets and HPKE: once or twice per handshake, about 1 us of a 50 to 100 us handshake. Handshake times before and after are within run-to-run noise (below) |
| ChaCha20-Poly1305 seal, 1200 B (QUIC packet) | 0.75 us | 3.01 us | 4.0x | Kept: per packet |
| ChaCha20-Poly1305 seal, 16 KiB (TLS record) | 8.1 us, 2.0 GB/s | 34.7 us, 0.47 GB/s | 4.3x | Kept: per record. libcrux's ChaCha20-Poly1305 is HACL*'s portable code; HACL*'s vectorised versions are not in libcrux's Rust |
| ML-KEM-768 encapsulate | 14.7 us | 22.0 us (libcrux, AVX2) | 1.5x | Kept: about 8% of an X25519MLKEM768 handshake (92 us), and aws-lc's ML-KEM is already partly proven |
| X25519 key pair and agreement | 31.8 us | 69.4 us | 2.2x | Kept: aws-lc's core is proven (s2n-bignum) |
| P-256 key pair and agreement | 55.2 us | 562 us | 10x | Kept |
| ECDSA P-256 sign | 18.5 us | 203 us | 11x | Kept |
| ECDSA P-256 verify | 64.0 us | 471 us | 7.4x | Kept |
| Ed25519 sign | 9.3 us | 53.5 us | 5.7x | Kept |
| Ed25519 verify | 37.2 us | 62.4 us | 1.7x | Kept |

Not benchmarked, and kept:

- Raw ChaCha20 for QUIC header protection: libcrux does not export it.
- RSA: libcrux-rsa (HACL*) does PSS only, not the PKCS #1 v1.5 that
  certificate signatures use, and signs from (n, d) without the CRT, which
  makes a private-key operation several times slower by construction.
- P-384: libcrux has none.

Handshakes, server side, `examples/bench.rs` (median of 9 runs of 300, us;
two runs each). Every full handshake seals two tickets and every resumed
one opens one:

| Group | Handshake | aws-lc tickets | libcrux tickets |
|---|---|---:|---:|
| X25519 | full | 70.9, 69.3 | 69.0, 76.6 |
| X25519 | resumed | 51.9, 50.9 | 51.2, 57.1 |
| P-256 | full | 99.7, 95.4 | 102.7, 102.1 |
| P-256 | resumed | 81.3, 77.2 | 83.0, 82.8 |
| X25519MLKEM768 | full | 92.2, 92.7 | 94.3, 91.4 |
| X25519MLKEM768 | resumed | 73.9, 72.6 | 79.1, 73.4 |

## Where the remaining gaps are

The unproven code that carries the most traffic is now ChaCha20-Poly1305
for records and packets, when a client prefers it: there is no verified
implementation within reach of aws-lc's speed (libcrux's is HACL*'s
portable code, 4x slower; HACL* has vectorised C that libcrux does not
export). AES-GCM is verilith-aes's wherever the CPU has the instructions
(every x86-64 server CPU since 2010 and every ARMv8 server core); on a CPU
without them it falls back to aws-lc, whose code there is unproven. Its
AArch64 kernels are proven and tested under qemu but not yet benchmarked on
Arm hardware. ML-KEM is the one case where moving would trade a partial
proof for a fuller one at a measurable cost (about 7 us per hybrid
handshake on this machine).
