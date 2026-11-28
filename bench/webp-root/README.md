# webp-root: table bits for WebP lossless prefix codes

`core::htable::build(lens, R)` makes a table of `2^min(longest, R)` entries.
Longer codes go to `decode_long`, which walks the code one bit at a time.
WebP passes `MAX_ROOT` = 10. The corpus is the 24 Kodak images (at the
commit in `bench/pins.sh`), encoded lossless by libwebp through Pillow at
methods 0, 4 and 6, 72 files in all.

## Counts (exact)

`sweep.sh 6 FILE...` builds an instrumented copy (`instrument.py`) with
6-bit tables, so every symbol longer than 6 bits takes the slow path.
`results/counts-root6.tsv` gives, per length, how many codes had it as
their longest and how many symbols of it were decoded. From those, for any
R ≥ 6:
- table entries filled = Σ codes × 2^min(longest, R)
- slow-path symbols = Σ symbols longer than R

## Model 1: slow path and fill only. Wrong.

The Brotli thread measured the slow path at about 37 cycles + 2 per bit and
filling at about 1 cycle per entry. With those, R = 12 comes out 36–52%
cheaper than R = 10, which predicts a faster decoder. Timing says otherwise:

| R | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|---|
| decode time vs 10 | +10.6% | +1.9% | −1.0% | 0 | +4.7% | +16.2% | +30.8% |

(`root-time.py`, `results/timing-cloud-x86.txt`.) What model 1 misses is the
lookups themselves: tables bigger than L1 make every symbol pay.

## Model 2: instructions and L1 misses

cachegrind's counts are deterministic too (`results/cachegrind.txt`):

| R | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|
| instructions (M) | 5239 | 5039 | 4880 | 4846 | 4908 |
| D1 misses (M) | 11.2 | 12.0 | 14.4 | 21.4 | 31.8 |

Least squares on the timings gives about 0.47 cycles per instruction and 4.3
cycles per D1 miss (an overlapped L2 hit, at 2.1 GHz). That fits every R to
within 1.3%, and puts the best at R = 9, only 1.1% faster than 10.
Measured on its own, with only the build call changed, R = 9 is 0.55% faster,
which is within this machine's noise. So `MAX_ROOT` stays at 10. Going above
10 is clearly worse on this data. It would also need new proofs, because
`try_lit` refills once for four 10-bit codes.

This is a fitted model: two constants from five timings. The counts it is
fitted on are exact. To check it on another machine, run the cachegrind
counts there and two or three timings.
