# crossover: size cutoffs from executed instructions

A kernel cutoff such as `VPCLMUL_MIN` ("the 512-bit CRC kernel from 512
bytes") compares two pieces of code at each input length. This tool works
that out from the instructions each one executes, without timing anything:

1. `src/main.rs` runs one call of a kernel on `n` bytes (`crossover <kernel> <n>`).
2. `trace.py`, under gdb, single-steps that call and records every
   instruction it executes, including the platform's `memcpy`.
3. `mca.py` gives each trace to llvm-mca for several CPU models and prints
   the cycles per call, both for one call on its own (`lat`) and for calls
   back to back (`tput`).
4. `cutoff.py` picks the cutoff whose worst ratio to the faster kernel, over
   every length and CPU model in the tables, is smallest.

The same binary, glibc, gdb and llvm-mca give the same numbers every time.
The tables in `results/` were made with LLVM 18.1.3, gdb 15.1 and glibc 2.39
on x86-64, with the crates built for plain x86-64 (no `target-cpu`), as they
ship:

```sh
cargo build --release
python3 mca.py crc512 crc256 256 4096 64 > results/crc512-vs-crc256.tsv
python3 mca.py memcpy wild 32 768 16 > results/memcpy-vs-wild-avx512.tsv
GLIBC_TUNABLES=glibc.cpu.hwcaps=-AVX512F,-AVX512VL,-AVX512BW,-AVX512DQ \
  CPUS=skylake,alderlake,znver3 python3 mca.py memcpy wild 32 768 16 > results/memcpy-vs-wild-avx2.tsv
python3 cutoff.py lat results/crc512-vs-crc256.tsv
```

Tracing needs a CPU that can run the kernel. The AVX-512 CRC kernel needs
AVX-512 and VPCLMULQDQ, and glibc's `memcpy` is whichever one glibc picks for
the CPU the trace runs on. `GLIBC_TUNABLES` above makes it pick the AVX2 one.

## What the model can and cannot decide

llvm-mca models the back end: ports, latencies and dependency chains, with
caches hot. It does not model the front end, so taken branches, calls and
returns cost nothing beyond their uops. It does not model branch prediction
or the stack engine either. A cutoff can be derived this way only when the
two sides differ in work the back end does.

- **`VPCLMUL_MIN = 512` (verilith-checksum): derived.** Both kernels are
  straight-line folds with the same few branches. What differs is
  carry-less multiplies and their latency chains. `cutoff.py lat` picks
  512, which keeps every call within 1.16x of the faster kernel from 256 to
  4096 bytes on Ice Lake, Sapphire Rapids and Zen 4 (mean 1.006x). Below
  512, the 512-bit kernel's tail loop, one serial 64-byte step at a time,
  loses on Intel whenever `n mod 256` is 128 or more. On Ice Lake that
  holds up to 1472 bytes.
- **`WILD_MAX = 192` (verilith-core `copy_lits`): not derivable this way.**
  The 32-byte loop against a `memcpy` call is decided mostly by the call,
  the return and memcpy's size-class branches, which are exactly what
  llvm-mca leaves out. With those free, `memcpy` wins from about 48 bytes,
  which is not credible. A wall-clock check on the shared cloud machine was
  too noisy to settle it (±50% between runs). The constant stays as chosen,
  and its comment says so.

## WILD_MAX by timing, with exact counts

Because the model can't settle `WILD_MAX`, two other measurements bound it.
`lz4hist` counts the literal runs `copy_lits` is given (exact): over all of
Silesia, only 7,390 of 12.9 million sequences have runs from 193 to 512
bytes. `wild-sweep.sh` times LZ4 decoding for several values, with the
builds interleaved (`results/lz4-wild-cloud-x86.txt`). Weighted by file
size, the values from 192 to 448 are within 0.9% of each other. That is
less than two builds of the same code can differ by, so 192 stays. The same
sweep on Apple silicon is still to be run.
