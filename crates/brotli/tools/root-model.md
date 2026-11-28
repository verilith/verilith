# Choosing the root table width

`prefix::pick_root` picks the width of the first-level (root) table of each
prefix code: 8, 9 or 10 bits. Any width is correct; the choice only affects speed.
This note records where its numbers come from and which derived models were
tried in their place.

## Costs that can be measured

| Cost | Value | Source |
|---|---|---|
| Symbol longer than the root (`decode_slow`) | about 37 cycles + 2 per bit | 2 mispredicted branches (about 17 cycles each on Golden Cove) plus a call; the bit loop is 1.97 cycles per iteration under `llvm-mca -mcpu=sapphirerapids` |
| Table fill (`build_sparse`) | about 1 cycle per entry | `llvm-mca -mcpu=sapphirerapids` on the fill loop: 1014 cycles per 1000 iterations |
| L1 data cache | 48 KiB, 5 cycles; L2 16 cycles | Intel optimization manual, Golden Cove / Raptor Cove |

The next bits of a well-matched prefix code are close to uniform, so codes
longer than `r` are reached with probability `sum over l > r of cnts[l] * 2^-l`.

## What the thresholds imply

The rule picks 8 bits if codes longer than 8 carry at most 1/64 of the
probability, else 9 bits if those longer than 9 carry at most 1/16, else 10.
At the slow-path cost above, that accepts up to 0.9 cycles per symbol to halve
a table from 9 to 8 bits, and 3.6 cycles from 10 to 9. That is the
price the rule puts on L1 pressure. The thresholds were set by measurement
(PR 206).

## Models tried instead (November 2026)

Each model picks, for each code, the `r` from 1 to 10 that minimises
slow-path cost + fill cost per symbol + an L1 miss term
`11 * (1 - 32 KiB / footprint)`. Here `footprint` is the size of the group's tables
if each used root `r`, and 32 KiB is L1 less the other tables, ring and input.
Results are decode time against the threshold rule, from 28 vbench
cases pinned to one core on cloud x86 (Emerald Rapids):

| Model | Footprint counts | Result |
|---|---|---|
| all trees equal | every tree in the group | 3% to 5% slower |
| context-map weighted | effective tree count from the context map | 4.3% slower |
| no cache term | this tree only | about 1% slower |

The first two shrink literal roots to 5 to 7 bits, because a large file
such as xml has about 185 literal trees in equal use by the context map. But
over any short stretch of output only a few of them are in use, so the real
L1 pressure is far lower than total size suggests. Which trees are used close
together in time is not known until the literals are decoded, after the
tables are built. Dropping the term is not exact either: it assumes the cache
cost is zero, and the measurement shows it is not.

## Trees in use together (second round)

Only one literal block type is current at a time, and it reads its 64-entry
row of the context map. So the trees in use together are the distinct trees in
a row, not the whole group. On the vbench files that number is 13 to 17, out
of up to 247 trees. The decoder can compute it (`row_trees`) as soon as the
context map is read, before any table is built. A row holds 64 entries for
literals and 4 for distances. For the command trees it is 1, one per block type.

Using that as the group size in the model above:

| Version | Result against the threshold rule |
|---|---|
| row count, recomputed for every tree | 5% slower (the counting itself was the cost) |
| row count, computed once per context map, 2 divisions per candidate | 1.0% to 1.3% slower |
| same, divisions taken out of the candidate loop | 0.65% to 1% slower |
| same, symbols per code estimated as 1/2 of the bytes for literals and 1/8 for commands and distances | 0.3% to 0.4% slower |

The remaining error is in how many symbols each code will decode, which sets
how far a table's fill cost is spread. Literal trees are read before the command
trees, so the literal count isn't known yet. Using the meta-block's byte count
overstates it: copies cover many bytes, and there are far fewer commands than
bytes. The 1/2 and 1/8 above are guesses, so they don't belong in the rule.
Differences under about 2% on a single case are within the variation between
two builds of the same code (layout). On dickens-4k, for example, forcing the
literal root from 10 to 9 accounts for 1.7% of a 3.5% gap.

The fill cost holds up when measured directly: building the dickens-4k literal tree
takes 0.43 ns more per extra entry (783, 1025 and 1240 ns at 8, 9 and 10
bits), about 1 cycle per entry.

The model is kept as a patch (`row-model.patch` in the project files).
To switch, it needs to beat the thresholds. The open question is a stream-derived estimate of
symbols per code, for example the previous meta-block's literal and command counts.

## Reproducing

- Slow path and fill: build with `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`.
  Then take the loop bodies of `decode_slow` and `build_sparse`
  from `objdump -d` and run them through `llvm-mca -mcpu=sapphirerapids`.
- Cache behaviour: build for `x86-64-v3` (valgrind can't run AVX-512), then
  run `valgrind --tool=cachegrind --D1=49152,12,64` on a vbench runner.
  The results are exact and repeat from run to run.
- Speed: run `bench/harness/vbench.py --only brotli-decode --cpu 2` with
  the two runners as the `brotli` and `vbrotli` binaries.
