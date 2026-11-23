# verilith-regex

A regular expression engine in Rust with RE2's syntax and RE2's guarantee
(matching takes time linear in the text, for every pattern), formally
verified with [Verus](https://github.com/verus-lang/verus).

Three things are proven, for every pattern and every text:

1. **The answer is right.** `Regex::new` accepts exactly the patterns the
   syntax (`src/syntax.rs`) accepts, apart from size limits, and a search
   reports exactly the match the semantics (`src/spec.rs`) defines: which
   match, where it ends, and where every capture group starts and ends.
2. **Time is linear.** A search of `n` bytes from position `from` makes at
   most `(n - from + 2) * step_cost(P, S)` loop iterations, where `P` is the
   number of instructions in the compiled program and `S` the number of
   capture slots. There is no backtracking, so patterns like `(a+)+b`
   cannot blow up.
3. **Memory is bounded.** The matcher's thread lists never hold more than
   `P` entries of `S` slots each, whatever the text, and its DFA and its
   table of stored steps never hold more than 256 states each. (While
   stored steps run, slot values sit in shared rows, at most `5 * P + 64`
   of them; that limit and the table's limit of 262,144 stored threads
   are checked by the code but are not part of a theorem.)

The proof covers the whole path: the parser, the compiler to a program for
an automaton, and the matcher (a Pike VM, with a lazy DFA in front of it
that passes over text where no match can be). Nothing in that path is assumed
or tested instead of proven; what is trusted is listed in
[TRUST.md](TRUST.md).

```rust
let re = verilith_regex::Regex::new(br"(?P<year>\d{4})-(?P<month>\d{2})").unwrap();
let m = re.captures_at(b"on 2026-11-19", 0).unwrap();
assert_eq!(&m[..], &[3, 10, 3, 7, 8, 10]); // start and end of each group
```

## Why RE2, and not POSIX

The target is RE2 through cre2, its C wrapper. POSIX `regcomp`/`regexec`
was the other candidate, and loses on three counts:

- POSIX asks for the leftmost-longest match with POSIX's submatch rules.
  Few implementations get those rules right, the standard is ambiguous in
  places, and no linear-time algorithm for them is simple enough to be
  worth trusting as a specification.
- RE2's rule (leftmost, then what a backtracking matcher would find first)
  has a short compositional definition, which is what `src/spec.rs` is.
  It is also the rule of Perl, PCRE, Python, JavaScript, Go and Rust's
  `regex`, so it is what callers expect.
- Programs choose RE2 for the linear-time guarantee. That guarantee is
  the kind of claim a proof is for.

## What is proven

**The semantics** (`src/spec.rs`, 220 lines). A regular expression is one
of eight forms: empty, one character from a set, an assertion, a capture
group, concatenation, alternation, `x?` and `x+` (each greedy or lazy).
`ms(r, s, i, c)` is the list of every way `r` matches the text `s` from
byte `i`, best first, each with where it ends and the capture slots.
`search(r, s, from, n)` is the first entry of that list at the first
start position at or after `from` that has one.

Text is bytes. A character class matches one well-formed UTF-8 sequence
whose code point is in the class. A byte that starts no well-formed
sequence matches no class, not even `.` or a negated class.

**The syntax** (`src/syntax.rs`). `parse(pattern)` gives the regular
expression a pattern stands for, the number of groups and their names, or
nothing if the pattern is not well-formed. It is written as a reference
parser over the bytes of the pattern.

**The theorems** (`src/lib.rs`):

- `Regex::new(pattern)` returns `Ok(re)` only with `parse(pattern) ==
  Some(Pat { re: re.re, .. })`, and returns `Err(e)` only if `parse(pattern)`
  is `None` or `e` is `TooBig`.
- `re.search_with(text, from, ..)` returns true exactly when
  `search(re.re, text, from, slots)` is some match `m`, and then the slots
  it filled are `m.caps`. It also returns the number of loop iterations it
  made (as a ghost value, erased when compiled), proven to be at most
  `(text.len() - from + 2) * step_cost(P, S)` with

  ```
  step_cost(P, S) = pike_cost(P, S) + dfa_cost(P) + memo_cost(P, S) + 2 + 34 * quick_cost(P, S)
  pike_cost(P, S) = 5 * (S + 3) * P + (S + 67) * P + (S + 67) + 7 * P + 7 * S + 12
  dfa_cost(P)     = 331 * P + 302
  memo_cost(P, S) = 2 * P * S + 805 * P + 2 * S + 4101
  quick_cost(P, S) = 400 * P + S + 2050
  ```

  The DFA's part and the stored steps' part are the worst case in which
  every byte needs a new transition or step computed. Each reads a byte
  at most once per search. The last part is for a start tried on its
  own (below): such tries read at most `4 * (n - from) + 67` bytes in a
  search between them, counted as they go.
  Computing a stored step runs on a budget of `400 * P + 2048`
  iterations, checked as it goes; a step that would need more is left to
  the Pike VM.

  Every iteration of every loop on the search path counts as one step,
  including the binary search for a code point in a class (at most 64
  steps per test).

**How it fits together.** The chain of proofs, each link checked by Verus:

| step | file | proven |
| --- | --- | --- |
| parser | `parse.rs` | computes `syntax::parse` |
| character classes | `class.rs` | ranges, union, negation, case folding and Unicode groups compute the sets `data.rs` defines |
| compiler, on paper | `cproof.rs` | the compilation scheme preserves the list of matches, in order |
| compiler, in code | `compile.rs` | emits exactly the scheme's program |
| matcher | `pike.rs`, `vmspec.rs` | reports the first match of the program's own semantics (`sem.rs`), within the step and memory bounds |
| skipping | `skip.rs` | no match starts at a byte the table rules out |
| second byte | `skip.rs` | no match starts at an ASCII byte unless the byte after it is one the pattern can go on with (`lemma_pair`) |
| required byte | `need.rs` | if every path to `Match` passes an instruction that consumes one ASCII byte and nothing else, no match starts before the run of bytes the pattern can consume that leads up to the next occurrence of that byte (`lemma_need_jump`), and none at all if there is no occurrence (`lemma_need_end`) |
| first-byte scan | `find.rs` | finds the next occurrence of a byte, of a pair of bytes each from a set of two, or of a byte in one of three ranges, 16 bytes at a time (SSE2, NEON) |
| lazy DFA | `dfa.rs` | no match starts anywhere the DFA passed with an empty state; at most 256 states |
| stored steps | `memo.rs` | a stored step, replayed, leaves the threads and their capture slots exactly as the matcher's own step would; at most 256 thread lists |

`scripts/verify.sh` runs Verus on all of it: 565 items verified, no
`assume`, no `admit`.

## Supported syntax

RE2's syntax, in UTF-8 mode with RE2's default options:

- Literals; `.`; `[...]` classes with ranges, negation, `[:alpha:]` and
  `[:^alpha:]` (the 14 POSIX names), and `\d \s \w \pN \p{Name}` inside.
- `\d \D \s \S \w \W` (ASCII, as in RE2).
- `\pN`, `\p{Name}`, `\PN`, `\P{Name}`, `\p{^Name}`: Unicode general
  categories and scripts, and `Any`. The tables are RE2's (Unicode 15.1).
- Escapes: `\a \f \n \r \t \v`, octal `\0` to `\377` and beyond (`\1` to
  `\7` need a second octal digit), `\xHH`, `\x{H...}`, any ASCII
  punctuation, and `\Q...\E`.
- Assertions: `^ $ \A \z \b \B`.
- Groups: `(...)`, `(?:...)`, `(?P<name>...)`, `(?<name>...)`.
- Flags: `(?i)`, `(?m)`, `(?s)`, `(?U)`, negation `(?-i)`, and scoped
  `(?i:...)`. Case-insensitive matching uses Unicode simple case folding.
- Repetition: `* + ?`, `{n}`, `{n,}`, `{n,m}` with counts up to 1000, and
  the lazy forms `*? +? ?? {n,m}?`.
- Alternation `|`.

Not supported, as in RE2: backreferences, lookahead and lookbehind.

Not supported, though RE2 has them: `\C` (match one byte), Latin-1 mode,
POSIX syntax mode and longest-match mode.

Limits: patterns may be any length, and groups may nest to any depth. The
compiled program has at most 262,144 instructions by default, about the
same as RE2's default `max_mem` of 8 MiB allows; `Regex::with_limit`
(`vregex_new_with_limit`, or `cre2_opt_set_max_mem` at 32 bytes an
instruction) sets another limit, up to 2^24 instructions, which is RE2's
ceiling too. A pattern over a limit is refused with `TooBig`.

## Differences from RE2

On 300,000 random patterns and texts (`tests/diff`), verilith-regex and RE2 agree
on whether the pattern is valid, whether it matches, and every group
boundary, except for about 1 case in 50,000. Those are all the same kind:

- **An empty iteration inside a nested loop.** `(a?(()|b))*` on `ab`: RE2
  reports the match `a`, verilith-regex reports `ab`. RE2's answer comes from its
  matcher visiting each instruction once per text position, which cuts a
  loop off after an empty iteration in an order that depends on the
  compiled program. verilith-regex's semantics uses a rule that can be stated
  without an automaton: after the first iteration, an iteration must
  consume at least one byte to count. Both rules terminate; they pick
  different matches in these cases, and usually only different group
  boundaries.

Other known differences:

- **Invalid UTF-8 in the text.** RE2 treats an invalid byte as U+FFFD-like
  input that `.` and negated classes match. In verilith-regex it matches no class.
- **Limits**, as above.
- **Error codes.** The cre2 API reports "too large" and "bad UTF-8" with
  RE2's codes and every syntax error as code 1; RE2's finer codes are not
  reproduced.

## C API

`include/vregex.h` is the native API: `vregex_new`, `vregex_search`,
`vregex_groups`, `vregex_group_index`, `vregex_error`, `vregex_free`.

With the `cre2-abi` feature the static library also exports these
functions of [cre2](https://github.com/marcomaggi/cre2) under cre2's
names, so it links in place of cre2 and RE2 with cre2's own header:

- `cre2_new`, `cre2_delete`, `cre2_pattern`, `cre2_error_code`,
  `cre2_error_string`, `cre2_num_capturing_groups`, `cre2_program_size`,
  `cre2_find_named_capturing_groups`;
- `cre2_match`, with all three anchors and any `startpos` and `endpos`;
- `cre2_opt_new`, `cre2_opt_delete` and every `cre2_opt_set_*` and getter.
  `case_sensitive`, `dot_nl` and `literal` work. `longest_match`,
  `posix_syntax`, `never_nl`, `never_capture` and Latin-1 make `cre2_new`
  fail if set away from RE2's default. The rest are accepted and have no
  effect (as in RE2, outside POSIX syntax mode).

Not provided: cre2's convenience matchers (`cre2_full_match` and
friends), replace, extract, quote-meta, the named-group iterator and sets.

`tests/capi/run.sh` builds one C driver twice, against cre2 + RE2 and
against verilith-regex, and compares what `cre2_match` reports for every anchor
and several options on 100,000 random cases. They differ on 8, all the
nested-loop case above.

The C API is glue outside the proof (see TRUST.md). Anchored matching is
done there: a search anchored at the start is the verified search,
accepted if its match starts at `startpos`; one anchored at both ends
searches for `(?:pattern)\z`.

## Performance

The Pike VM tracks every capture group as it goes, which is slow, so two
proven shortcuts run in front of it while no thread is alive, and a third
speeds up the VM itself:

- **Start bytes** (`src/skip.rs`). The search passes over every byte that
  cannot begin a match, one table lookup per byte. `lemma_skip` proves
  that no match starts at such a byte. When only one byte can begin a
  match, the search for it runs 16 bytes at a time with SSE2 or NEON,
  and 64 at a time while the byte stays absent
  (`src/find.rs`, proven from the instruction specifications listed in
  TRUST.md). A second table says which bytes can follow the first
  character of a match, so a start whose next byte is not among them is
  passed over too (`lemma_pair`). When the first byte is one of at most
  two and the second is one of at most two, as in `http` or in
  `(?i)copperfield`, the search looks for the two together, 16 places at
  a time. Otherwise, when the bytes that can begin a match are few and
  none is a space or a lower-case letter (digits, capitals, the first
  letters of a handful of names), the compiler covers them with up to
  three byte ranges, split at the widest gaps, and the search looks for
  a byte in those ranges 16 at a time (`find_rng`). The ranges may hold
  more bytes than the table flags: a byte found is still checked against
  the table.
- **A lazy DFA** (`src/dfa.rs`). Its states are sets of program
  instructions, built as the text demands them and kept between searches.
  It only answers "no match starts before here": it treats every
  assertion (`^`, `\b`, ...) as true, so its sets are never too small, and
  when a set comes up empty every start so far is ruled out
  (`lemma_flows_empty`). When a set holds a match it stops and hands the
  last position not ruled out to the Pike VM, which finds the match and
  its groups exactly. It reads ASCII bytes only and stops at anything
  else, and it stops for good at 256 states or about 4 MiB of state sets;
  the Pike VM carries on from wherever it stops, so none of this changes
  the answer or the linear bound.
- **A byte every match needs** (`src/need.rs`). `[\w.+-]+@[\w-]+\.[\w.-]+`
  cannot match without an `@`, nor `(\w+)=(\w*)(&|$)` without an `=`.
  The compiler looks for such a byte: one that some instruction
  consumes alone, such that `Match` cannot be reached from the start
  once those instructions are taken away. It tries the rarer bytes
  first and leaves the most common letters, the space, the newline, `.`
  and `,` alone. A checker pass over the candidate set of reachable
  instructions is what the proof rests on, not the search for it. With
  such a byte, whenever the DFA has no thread alive it finds the next
  occurrence 16 or 64 bytes at a time, walks back over the bytes the
  pattern could consume at all, and resumes from there; with no
  occurrence left the search is over. Each byte is scanned forward once
  and walked back over once per search (the `+ 2` in the bound above).
  It is used when the first bytes of a match give no fast scan of their
  own.
- **Stored steps** (`src/memo.rs`). What a step of the Pike VM does to
  its thread list depends only on which instructions the threads are at,
  whether a match is already known, the byte, and the kind of the next
  byte (for `\b` and `$`): which threads survive, in what order, which
  thread each one continues, and which capture slots it sets to the
  current position. The search computes that once per such situation,
  without slot values (`sfull`, proven equal to the VM's step by
  `lemma_sfull` and `lemma_cfull`), keeps it in a table between searches,
  and from then on replays it. Threads do not carry their slots while
  this runs: each points at a shared row of slot values plus the slots it
  has set since, and a row is written only when a thread lives on with
  slots set. It handles ASCII bytes and patterns of up to 31 groups, and
  the table stops growing at 256 thread lists or 262,144 stored threads;
  anything else falls back to the VM's own step, one byte at a time.
  Before it replays steps with their threads, the search follows the
  same table by list number alone, touching no thread, for as long as
  no step reaches a match. It stops at the first step that leaves no
  thread of an earlier start alive: no thread then leads to a match
  (`lemma_idle`), so the run ends with no thread at all and the search
  for a start (skip tables, DFA) takes over again, since it passes over
  text faster. So groups are tracked from about where the match begins
  and not from wherever the search took up. The run reads each byte at
  most once per search (one more iteration per byte in the bound above).
  When the threads of a step all continue the same thread, which is the
  usual case inside a match, no list is written either: the list is
  that thread's row plus the step's own record of which slots each
  thread sets, and a run of such steps costs one read of a small table
  per byte (`urun`). Lists are written out only for a step whose threads
  come from two or more threads.
  When the search for a start stops at a byte with no thread alive, that
  start is first tried on its own (`quick`): its threads are followed
  through the stored steps of lists that take no new start, as one row,
  with no thread list built at all. If it reaches a match and no thread
  is left, that match is the answer; if every thread dies first, the
  search goes on from the next byte; if two threads must be kept apart,
  the try is dropped and the lists take over from the same byte. A try
  that is dropped has read bytes for nothing, so the search keeps score
  and mostly stops trying on patterns and texts where it does not pay.

RE2 works differently once a match is near: after its DFA it finds the
exact bounds of the match with a second, reverse DFA and computes groups
over the match alone, with a one-pass engine where the pattern allows,
while verilith-regex runs the Pike VM, on stored steps, from the last position
its DFA could not rule out. In vbench's
`regex-re2` comparison (12 patterns over English text and URLs, finding
every match with its groups), on the project's reference machine (a Mac),
verilith-regex at commit 4a5792a gives the same results as RE2 in all 36 cases
and is faster in all 36. By pattern (geometric mean over the three
inputs):

| pattern | verilith-regex speed, RE2 = 1 |
| --- | --- |
| email | 123 |
| captures (`(\w+)=(\w*)(&|$)`) | 31 |
| digits (`[0-9]{2,4}`) | 12.4 |
| alternation (a list of names) | 9.67 |
| class-run (`[A-Z][a-z]+ [A-Z][a-z]+`) | 4.56 |
| url-host | 4.41 |
| literal-nocase | 2.71 |
| word-suffix (`\b\w+ing\b`) | 2.65 |
| unicode-words (`\p{Lu}\p{Ll}+`) | 1.98 |
| no-match (a rare first byte) | 1.79 |
| literal | 1.60 |
| tld (`\.(?:com|org|net)\b`) | 1.44 |

The geometric mean over all 36 cases is 5.3. Read it with care: a few
cases carry much of it. Email on all three inputs and captures on the
two English texts run at 90 to 150 times RE2 because those inputs hold
almost no `@` or `=`, so the search is little more than a scan for that
byte, and digits on English text runs at 20 to 40 times RE2 for the
same kind of reason: digits are rare there. Those ratios say as much
about the inputs as about the engine. Leaving email and captures out,
the other ten patterns are between 1.4 and 12.

The closest case is tld on the shorter English text, at 1.3. Literal-nocase
and captures on a file of URLs, where matches cover much of the text,
are at 1.4 and 1.5.

## Building and testing

```sh
cargo build --profile release-abort                 # Rust library and libverilith_regex.a
cargo build --profile release-abort --features cre2-abi
cargo test --profile release-abort
scripts/verify.sh                     # needs cargo-verus, see the script
tests/capi/run.sh                     # C API; see the script for RE2
scripts/check_tables.sh RE2_CHECKOUT  # the Unicode tables are RE2's
```

`tests/diff/diff.py` compares verilith-regex with RE2 on fixed and random cases;
its header says how to build the two programs it needs.

## Licence

Licensed under either of the [Apache License, Version 2.0](LICENSE-APACHE)
or the [MIT license](LICENSE-MIT), at your option.

The Unicode tables in `src/tables.rs` are generated from RE2's, which are
under the BSD licence in [LICENSE-re2](LICENSE-re2).
