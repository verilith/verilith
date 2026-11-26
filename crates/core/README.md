# verilith-core

Formally verified ([Verus](https://github.com/verus-lang/verus)) building
blocks shared by the Verilith libraries
([verilith-zlib](https://github.com/verilith/verilith/tree/main/crates/zlib),
[verilith-webp](https://github.com/verilith/verilith/tree/main/crates/webp),
[verilith-dns](https://github.com/verilith/verilith/tree/main/crates/dns),
[verilith-http](https://github.com/verilith/verilith/tree/main/crates/http),
[verilith-json](https://github.com/verilith/verilith/tree/main/crates/json),
[verilith-url](https://github.com/verilith/verilith/tree/main/crates/url)). Each piece used to
live, with its proofs, in one or two of those crates; it now lives here
once, and the libraries import it.

`cargo verus verify` checks 272 functions with no errors.

| module | what it has | used by |
| --- | --- | --- |
| `prims` | memory primitives: unchecked `get`/`set` on `u8` and `u32` slices, `store_at`, unaligned little-endian loads, 8-byte copies and fills, slice copies, `extend`, fallible zeroed allocation (`alloc_u8`, `alloc_i16`, `alloc_u32`) | verilith-zlib, verilith-webp, verilith-http, verilith-json, verilith-gif, verilith-tiff, verilith-png, verilith-jpeg |
| `lz` | LZ77 over byte slices, for decoders that write into a caller's buffer and for compressors: `lz_copy` (what a match copy means, overlap included), `copy_match` (any offset, 16 bytes at a time where there is room: offsets under 8 are widened by overlapping 8-byte moves), `copy_match24`/`copy_match16` (short matches from at least 8 back, no loop), `copy_match_wild` and `copy_lits_wild` (32 bytes at a time into room the caller has, with no test before the first 32), `copy_lits`, `eq_len` (match length, 8 bytes per compare), `load32`, and the lemmas that tie them to `lz_copy` (`lemma_matched`, `lemma_lz_copy_is`) | verilith-lz4, verilith-snappy |
| `tail` | `Tail`: a byte vector appended to without capacity tests. Room is reserved once, and each append's precondition, proven by the caller, says the bytes fit. Appends from a slice and from the vector's own earlier bytes, copied 16 bytes at a time | verilith-zstd |
| `spare` | a `Vec`'s spare capacity (uninterpreted, as vstd does not model it), with `reserve_spare`, `len_spare`, and stores into reserved room without a capacity check: `push_spare`, `append4_spare`, `append8_spare`, `append_slice_spare`, plus `truncate_spare` and `set_spare` | verilith-json, verilith-zlib |
| `bytes` | big- and little-endian integers in byte strings as spec functions; `read_u16`/`read_u32` proven to return them | verilith-dns, verilith-zlib (spec) |
| `cursor` | `Cursor`, a bounds-checked reader over a slice: `read_u8`, `read_u16_be`, `read_u32_be`, `peek_u8`, `take`, `skip`, `split`, `slice_from` | verilith-x509 |
| `bits` | bit strings packed least significant bit first (DEFLATE, WebP lossless, PNG): `bits`, `code_bits`, and the arithmetic proofs about them; `u64` masks and shifts as bit readers use them (`lowmask`, `lemma_and_mask`, `lemma_shr_bits`, `lemma_or_byte`) | verilith-zlib, verilith-webp, verilith-brotli, verilith-zstd |
| `huffman` | canonical Huffman codes (RFC 1951 §3.2.2): `count`, `first_code`, `left` (Kraft), `decode`, `valid_code`, the proofs that make lookup tables exact, and `reverse` | verilith-zlib, verilith-webp, verilith-brotli |
| `htable` | a verified two-level decoding table builder (`build`, and `build_sparse` for callers that already know which symbols have a code) and slow-path decoder for canonical codes, with WebP's 2328-symbol alphabets and the CVE-2023-4863 overflow bound | verilith-webp, verilith-brotli |
| `utf8` | well-formed UTF-8 (Unicode Table 3-7), the three-byte local condition SIMD validators check, its proof, simdjson's lookup tables with the proof that they compute it (`lemma_lookup`, `lemma_err_lane`), and a verified scalar validator | verilith-json, verilith-text |
| `num` | decimal digits: `is_digit`, `digits_end`, `dec_value`, `decimal`; `parse_u64_dec` (checked) and `push_decimal` | verilith-json, verilith-url, verilith-dns |
| `binary64` | IEEE 754 binary64 as a model in spec integers (in the style of Coq's Flocq): what each bit pattern is worth as an exact rational, round to nearest, ties to even (`rne`), proofs that rounding depends only on the value and that exact products and quotients of equal values are equal, that `u64 as f64` is exact below `2^53`, and `P10`, the exact doubles `10^0..=10^22`; `mul`, `div` and `from_u64` on bit patterns | verilith-json |
| `sort` | `order_by`: a stable merge sort of the positions `0..n` by a caller's comparison closure, proven to return a permutation (as multisets) in which each position compares `le` the next; the comparison need only be total | verilith-archive, verilith-zlib |

verilith-webp and verilith-brotli share the table builder in `htable`. verilith-zlib keeps its own:
it builds a different layout (DEFLATE's flagged length/distance entries) on
top of the shared code spec and proofs here.

## Using it

```toml
[dependencies]
verilith-core = { git = "https://github.com/verilith/verilith", rev = "..." }
vstd = "=0.0.0-2026-11-22-0344"
```

Spec functions are erased in a normal build, so import them under
`#[cfg(verus_only)]` (or `verus_keep_ghost`), as the libraries do.

Without the default `std` feature the crate is `no_std` and needs only
`alloc` (`verilith-core = { ..., default-features = false }`, with vstd's
`default-features = false, features = ["alloc"]`).

CRC-32, CRC-32C and Adler-32 used to live here as `verilith_core::checksum`;
they are now their own crate,
[verilith-checksum](https://github.com/verilith/verilith/tree/main/crates/checksum).

## Trusted base

What the proofs here assume rather than prove:

- `src/prims.rs`, the `external_body` functions only: `load_u64_le`,
  `copy8`, `copy16`, `move8` (an 8-byte load then store, so its ranges
  may overlap), `copy16_in`, `fill8`, `copy_in`, `copy_to_front`, `copy_within`,
  `alloc_u8`, `alloc_i16`, `alloc_u32`, `pick` (one of two numbers, chosen without a branch) and
  `copy16_pick` (`copy16_in` or `copy16`, with the source chosen without a
  branch). Each is one line whose effect its `ensures` states, except
  `copy16_pick`, which is six.
  (`get`, `get16`, `get32`, `set`, `set16`, `set32`, `store_at` and `extend` are verified
  against vstd's specs of `get_unchecked` and `extend_from_slice`.)
- `src/spare.rs`, all of it: the uninterpreted `spare` and its nine
  functions (`len_spare`, `reserve_spare`, `reserve_spare_plus`,
  `push_spare`, `append4_spare`, `append8_spare`, `append_slice_spare`,
  `truncate_spare`, `set_spare`). The stores write through a raw pointer
  into room `reserve_spare` made; what is assumed is that `spare(v)` is
  `v.capacity() - v.len()` and that each store stays within the bounds its
  `requires` gives. They were verilith-json's (and one verilith-zlib's).
- `src/tail.rs`, all of it: the type `Tail` and its seven functions
  (`take`, `put_back`, `len`, `append_from`, `append_from32`,
  `append_within`, `append_within32`). The appends write through a raw
  pointer into capacity reserved by `take`; what is assumed is that each
  stays within the bounds its `requires` gives, with `cap()` read as the
  vector's capacity. `tests/basic.rs` compares them with `Vec` appends
  over every length and offset up to 100.
- `src/binary64.rs`, the three `external_body` functions `mul`, `div`
  and `from_u64`: each is one line (`f64` `*`, `/` or `u64 as f64` on bit
  patterns) whose `ensures` says the result is the exact result rounded to
  nearest, ties to even (IEEE 754-2019 §4.3.1 and §5.4.1). This holds
  where Rust's `f64` is IEEE 754 binary64 in its default environment,
  which is every target with SSE2 or NEON. Everything else in the module,
  including what rounding means for the values the callers care about, is
  proven from the model.
- The specs: the format and rounding definitions at the top of
  `binary64.rs`, and the spec functions
  at the top of `bits.rs`, `huffman.rs`, `utf8.rs`, `num.rs` and
  `bytes.rs`.
- Verus, Z3 and the Rust compiler.

## Verifying

```sh
./scripts/verify.sh
```

needs `cargo-verus` from Verus commit
1ce6a59bd72713cf486a7660097fe5ac57519617 on `PATH` and z3 (via
`VERUS_Z3_PATH` or next to the verus binary). CI builds it from source.

## License

Licensed under either of the [Apache License, Version 2.0](https://github.com/verilith/verilith/blob/main/crates/core/LICENSE-APACHE)
or the [MIT license](https://github.com/verilith/verilith/blob/main/crates/core/LICENSE-MIT), at your option.
