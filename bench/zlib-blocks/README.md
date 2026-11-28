# zlib-blocks: block and chunk sizes from exact output sizes

Compressed size is a function of the input and the code alone, so a sweep
over a size constant measured in output bytes is exact: no timing, no noise,
the same numbers on every machine. The corpus is the 12 Silesia files
(211 MB) at the commit pinned in `bench/pins.sh`.

```sh
cd /path/to/silesia
bench/zlib-blocks/sweep.sh "4096 8192 10240 12288 14336 16384 20480 24576 32768 65536" *   # results/block-tokens.tsv
bench/zlib-blocks/target/release/par 32,64,128,256,512,1024,2048 1,6,9 *                 # results/par-chunk-sizes.tsv
bench/zlib-blocks/par-cost.sh dickens samba                                               # results/par-chunk-work.tsv
```

## `deflate::MAX_TOKS = 16384`: tokens per block

This is zlib's `lit_bufsize` at its default `memLevel` of 8. Output over all
of Silesia, against 16384:

| tokens | 4096 | 8192 | 10240 | 12288 | 14336 | 16384 | 20480 | 24576 | 32768 | 65536 |
|---|---|---|---|---|---|---|---|---|---|---|
| level 1 | +0.310% | −0.014% | −0.037% | −0.029% | −0.010% | 0 | +0.035% | +0.085% | +0.177% | +0.479% |
| level 6 | +0.329% | −0.008% | −0.031% | −0.029% | −0.015% | 0 | +0.045% | +0.084% | +0.171% | +0.432% |
| level 9 | +0.361% | +0.013% | −0.023% | −0.026% | −0.020% | 0 | +0.030% | +0.073% | +0.163% | +0.442% |

The best fixed size is 10240 to 12288 tokens, 0.03% smaller than 16384. That
is too little to be worth more Huffman table builds, so 16384 stays.
Each file's own best size differs from 16384 by up to 0.57% (mozilla is
best at 4096, webster and x-ray at 65536). So the gain available is in
choosing block ends from the data, as libdeflate does, not in the constant.

## `par::CHUNK = 256 KiB`: parallel compression chunks

**Size (exact).** Cutting the input costs very little. Against one chunk,
over Silesia:

| chunk | 32K | 64K | 128K | 256K | 512K | 1M | 2M |
|---|---|---|---|---|---|---|---|
| level 6 | +0.118% | +0.063% | +0.048% | +0.017% | +0.007% | +0.004% | −0.002% |
| level 9 | +0.109% | +0.050% | +0.034% | +0.013% | 0.000% | −0.003% | −0.005% |

At level 1, the piecewise path is 0.20% to 0.32% larger at every chunk size,
so that difference is not caused by chunking.

**Work per chunk (deterministic count).** Each chunk adds about 1.0 to 1.5
million instructions (cachegrind, level 6): priming with the 32 KiB before
it, and the flush. That is as much work as compressing 7 to 16 KiB.

**Balance (model).** Say T equally fast threads compress k = ⌈n/c⌉ chunks.
Then the time taken is ⌈k/T⌉ × (c + per-chunk work). Over inputs from 512 KiB
to 64 MiB and T from 2 to 16, compare each fixed c with the best c for that
(n, T):

| c | 32K | 64K | 128K | 256K | 512K |
|---|---|---|---|---|---|
| mean ratio | 1.13–1.31 | 1.06–1.13 | 1.10 | 1.25–1.30 | 1.69–1.82 |

On this model, 64 to 128 KiB beats 256 KiB. With 256 KiB, inputs shorter
than T × 256 KiB leave threads idle. The model leaves out unequal cores
(Apple's performance and efficiency cores), scheduling and cache effects,
so the change needs a wall-clock check on a machine with many cores before
it is made. `CHUNK` stays at 256 KiB for now. The chunk size must not depend
on the thread count, because the output would then change with it.
