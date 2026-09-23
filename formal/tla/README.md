# TLA+ models of the sponge and AEAD-decryption logic

This directory contains two PlusCal/TLA+ models of `ocaml-ascon`, checked with
TLC (tla2tools 1.7.4 / TLC 2.19), and the scripts to re-run every check.

| File | Models |
| --- | --- |
| `Sponge.tla` | `lib/internal/sponge.ml` (absorb / finish / squeeze), `Hash256.get`, the `of_state (finish_state _)` step of `Cxof128.init`, the OCaml heap, persistence, and two OCaml 5 domains |
| `AeadDecrypt.tla` | `Aead128.decrypt`, `Aead128.decrypt_combined` (`lib/ascon.ml:116-175`) and `Constant_time.equal` (`lib/internal/constant_time.ml`) against an adversary |
| `*.cfg` | one file per TLC configuration that was run (see the tables below) |
| `run.sh` | runs every configuration; see [Running](#running) |

Both modules contain their PlusCal source in a comment followed by the
up-to-date `pcal.trans` translation (`run.sh` fails if the translation is
stale).  Properties are defined after the translation.

All results below come from completed TLC runs; nothing is claimed that TLC
did not check.

## Running

```sh
cd formal/tla
./run.sh                      # every configuration that must pass (+ translation check)
./run.sh --expected-failures  # the documented permutation-economy findings (must FAIL)
./run.sh --witnesses          # non-vacuity: every NoW_* "unreachable" claim must be refuted
./run.sh --all                # all three
./run.sh Sponge_rate8         # a single configuration
```

`JAVA` (default `java`), `TLA2TOOLS` (default
`~/.local/share/tlaplus/tla2tools.jar`), `WORKERS` (default `auto`) and
`JAVA_OPTS` (default `-XX:+UseParallelGC -Xmx8g`) can be overridden.  TLC
runs in a temporary copy of this directory with a temporary `-metadir`, so no
`states/` directories or trace files are written into the repository.
`run.sh` exits non-zero on any unexpected result; `--expected-failures`
succeeds only if each expected-failure configuration reports exactly the
documented invariant violation.

### Results of the final `./run.sh --all` run

TLC 2.19 (tla2tools 1.7.4), `WORKERS=6`, Apple ARM64, 10 cores shared with
other jobs (wall-clock times are indicative only); total 26 min 25 s.  Every
PlusCal translation was confirmed up to date.

**Configurations that must pass** (all passed: "Model checking completed.
No error has been found."):

| Configuration | Model / bounds | Generated | Distinct | Depth | Time |
| --- | --- | ---: | ---: | ---: | ---: |
| `Sponge_rate2` | Rate 2, exact XOR over bytes {0,1}, 1 domain, 3 ops, absorb 0..4, squeeze 0..3, all ops; + `Termination` | 3,092,823 | 2,870,167 | 116 | 7 min 48 s |
| `Sponge_rate2_tagged` | Rate 2, distinct-symbol bytes, 1 domain, **5 ops**, absorb 0..3, squeeze 0..3 | 13,625,404 | 12,607,945 | 192 | 9 min 56 s |
| `Sponge_rate3` | Rate 3, distinct symbols, 4 ops, absorb 0..6, squeeze 0..6 | 2,537,613 | 2,355,783 | 170 | 1 min 34 s |
| `Sponge_rate8` | **Rate 8 (real)**, distinct symbols, 3 ops, absorb 0..17, squeeze {0,1,7,8,9,15,16,17}, `get` = 32 bytes | 713,794 | 662,652 | 188 | 33 s |
| `Sponge_concurrent` | Rate 2, distinct symbols, **2 domains × 2 ops**, absorb 0..3, squeeze 0..3 | 17,038,860 | 8,740,158 | 155 | 3 min 46 s |
| `Sponge_lazy` | lazy variant, Rate 2, 4 ops; + `PermMinimal`, `OpPermMinimal`, `HashGetMinimal` | 494,126 | 457,271 | 150 | 16 s |
| `Sponge_lazy_rate8` | lazy variant, Rate 8, 3 ops, absorb 0..17; + the three minimality invariants | 711,266 | 660,124 | 185 | 15 s |
| `AeadDecrypt_tag2` | tag 2 B, word 2 B, ciphertexts 0..9 B, tags 0..3 B over {0,1,2}, combined 0..6 B, `equal` on all strings 0..3 B over {0..3}; + `Termination` | 175,977 | 157,827 | 28 | 10 s |
| `AeadDecrypt_tag3` | tag 3 B, word 2 B, ciphertexts 0..9 B, tags {0,2,3,4} B over {0,1}, combined 0..7 B, `equal` 0..4 B over {0,1}; + `Termination` | 40,893 | 37,091 | 29 | 2 s |

The Sponge pass configurations check `TypeOK BufferedRange OffsetRange
BufferContents AbsorbRefinement SqueezeRefinement OutputCorrect
SqueezeConcat ZeroSqueezeNoop AbsorbLoopInv SqueezeLoopInv Persistence
NoWriteToPublished NoUserAliasing WritesOnlyFresh RaceFree
AbsorbPermMinimal` plus `EagerExtraPermExact` (eager) or `PermMinimal
OpPermMinimal HashGetMinimal` (lazy).  The AEAD configurations check every
invariant of §2.2.

**Expected failures** (`--expected-failures`; both reported exactly the
documented violation, see finding F1):

| Configuration | Invariant | TLC result |
| --- | --- | --- |
| `Sponge_economy_get` | `HashGetMinimal` | "Error: Invariant HashGetMinimal is violated." — 63-state trace, 63 states generated |
| `Sponge_economy_squeeze` | `PermMinimal` | "Error: Invariant PermMinimal is violated." — 25-state trace, 126 generated / 121 distinct |

**Non-vacuity witnesses** (`--witnesses`): all 26 `NoW_*` predicates were
refuted, i.e. every configuration really reaches the situations its
properties talk about — e.g. absorbing from `buffered = Rate - 1` a chunk that
fills the buffer, absorbs a full block from the input and leaves a tail
(Rate 2, 3 and 8); a message of exactly one block followed by the full
padding block (Rate 2 and 8); squeezes starting mid-block and crossing a
boundary; a squeezing context at a block boundary; two non-empty consecutive
squeezes and the matching single squeeze (`SqueezeConcat` antecedent,
40-state witness); zero-length squeezes; absorption after `reinit`; a held
context extended in two different ways; both domains simultaneously inside
library code on the *same* context, each having written its own fresh
objects (7-state witness); a domain working on a context the other domain
published while that domain is itself mid-operation (14 states); AEAD `Ok`
after full blocks plus a tail of each kind, `Authentication_failure`, both
`Invalid_tag_length` paths, a successful `decrypt_combined`, and
`Constant_time.equal` on equal strings and on strings differing only in the
last byte.

---

## 1. `Sponge.tla`

### 1.1 What is modelled

Every operation a user can apply to a held context, each written at OCaml
statement granularity (one PlusCal label per heap-touching statement; purely
local statements are folded into the neighbouring label):

* `absorb` — `Sponge.absorb` (sponge.ml:18-40) = `Hash256.feed`,
  `Xof128.absorb`, `Cxof128.absorb`;
* `finish` — `Sponge.finish = squeezing_of_state (finish_state _)`
  (sponge.ml:42-53) = `Xof128/Cxof128.start_squeezing`;
* `squeeze` — `Sponge.squeeze` (sponge.ml:55-77) = `Xof128/Cxof128.squeeze`;
* `get` — `Hash256.get` (ascon.ml:187-189): `finish` then
  `squeeze digest_size`, discarding the squeezing context;
* `reinit` — `Sponge.of_state (Sponge.finish_state _)`, the step of
  `Cxof128.init` (ascon.ml:237-243) that finalises the customization string and
  starts a fresh message with an empty buffer.

`Sponge.init` (sponge.ml:9-12) only touches objects it allocates; its result
(a permuted IV state and a zero buffer) is the initial content of the pool.

**Heap.** `heap` maps object ids `<<allocator, n, "st"|"by">>` to `State.t`
values or `bytes` values.  A context value is a record of object ids plus the
immutable int field (`buffered` or `offset`).  `State.copy`, `Bytes.copy`,
`Bytes.create` (content: a distinguished *uninitialised* byte) and
`Bytes.make` allocate; `Bytes.blit`, field writes (`state.x0 <- ...`),
`Permutation.p12` and `Bytes.unsafe_set` write.  Every write is recorded in
the ghost write set `wr[d]` of the running operation.

**User and pool.** `pool` is the set of every context value ever returned to
the user, each with its ghost meaning and a deep snapshot of the objects it
references.  Each operation takes *any* pooled context of the right kind, so
old contexts are continued again and again (branching / persistence).  User
inputs to `absorb` and outputs of `squeeze` are user-owned `bytes` objects.

**Domains.** `Domains` is a set of PlusCal processes (OCaml 5 domains).  Each
runs `MaxOps` operations; steps of different domains interleave at statement
granularity and a context published by one domain can be picked up by the
other while it is itself mid-operation.

### 1.2 Abstractions and why they are sound for this code

* **Symbolic permutation.**  A `State.t` value is
  `[perms |-> <<m_1, ..., m_k>>, acc |-> m]`: the XOR masks applied to `x0`
  before each of the `k` `p12` calls since the IV, and the mask XORed into
  `x0` since the last `p12`.  For *any* fixed permutation this pair determines
  all five words (`p12` maps `(perms, acc)` to `(perms ++ <<acc>>, 0)`), and
  byte `j` of `x0` is `P(perms)[j] XOR acc[j]`, represented by the free atom
  `<<"P", perms, j>>` XORed with `acc[j]`.  Hence *symbolic equality implies
  concrete equality* for the real Ascon-p[12]; the model checks the
  index/buffer/offset/padding logic, not cryptography.  Because the atoms are
  free, the symbolic outputs are distinct whenever the permutation inputs
  differ, i.e. the model treats p12 as injective (an ideal permutation), which
  is what makes a wrong mask or a wrong number of permutations observable.
* **Bytes.**  A byte is a finite set of atoms and XOR is symmetric difference
  (the free GF(2) vector space).  In *alphabet* mode (`Tagged = FALSE`) byte
  `n` is the set of its set bits, so XOR is exactly bytewise XOR — including
  the real collision between data byte `0x01` and the padding byte `0x01`.  In
  *tagged* mode every input byte is a fresh atom `<<"in", <<domain, op>>, j>>`.
  `sponge.ml` is data-independent (no branch or index depends on a byte
  value; bytes are only moved and XORed with the constant padding byte at a
  data-independent position), so by the data-independence argument
  (Wolper, 1986) distinct symbols are the most discriminating input: any
  mis-routed, dropped, duplicated or stale byte changes some symbol.
* **Rate.**  `sponge.ml` hard-codes the rate as the literal `8` at lines 7,
  25, 29, 32, 34, 63 and 73 (line 65's `8 *` converts bytes to bits); the
  model replaces each by `Rate`, and endian.ml's `load_partial_le`/`padding`
  by byte-position versions.  All control flow compares lengths and offsets
  with `Rate` using `min`, `+`, `-`, `=`, `>=`; there are no other rate-specific
  constants.  The case structure (buffered = 0 or not; the first block is
  filled or not; zero, one or several full blocks from the input; a tail or
  not; the offset reaches the rate or not) is the same for every `Rate >= 2`,
  so small rates exercise every path.  `Rate = 3` removes the `Rate - 1 = 1`
  coincidence of `Rate = 2`, and `Rate = 8` itself is checked directly with
  distinct-symbol bytes (for 3 operations, absorb lengths 0..17, i.e. every
  `(buffered, length)` combination that fills, crosses one or two blocks and
  leaves any tail).  This is a small-scope argument, not a proof for
  unbounded histories.
* **Bounds.**  Bounded number of operations per domain, absorb lengths and
  squeeze lengths (see the configuration table).  `Sys.max_string_length`
  and negative lengths (sponge.ml:56-57, the `valid_length` wrappers) are not
  modelled.
* **Memory model.**  Interleavings are sequentially consistent and returning a
  context publishes it to the other domain.  That corresponds to handing
  contexts between domains through any synchronising mechanism
  (`Domain.spawn`/`join`, `Mutex`, `Atomic`, channels); see finding F3 for
  racy publication.

### 1.3 Correspondence between PlusCal labels and OCaml

| Label | OCaml (lib/internal/sponge.ml unless noted) | Heap effect |
| --- | --- | --- |
| `pick` | user code: choose a held context and arguments; allocate the input `bytes` | user allocation |
| `ab_copy_state` | 19 `let state = State.copy context.state` | read published state, allocate |
| `ab_copy_buf` | 20-23 `Bytes.copy context.buffer`, `buffered`, `input_offset`, `input_length` | read published buffer, allocate |
| `ab_if` | 24-25 `if !buffered <> 0`, `take = min (8 - !buffered) input_length` | read input length |
| `ab_blit1` | 26-29 `Bytes.blit input 0 buffer !buffered take`, `buffered +=`, `input_offset :=`, `if !buffered = 8` | write fresh buffer |
| `ab_blk1_xor` | 30 → `absorb_block` 15 `x0 <- x0 xor load64_le buffer 0` | write fresh state |
| `ab_blk1_p12` | 30 → `absorb_block` 16 `p12 state`; 31 `buffered := 0` | write fresh state |
| `ab_loop` | 32 `while input_length - !input_offset >= 8` | — |
| `ab_blk2_xor` | 33 → 15 `x0 <- x0 xor load64_le input !input_offset` | read input, write fresh state |
| `ab_blk2_p12` | 33 → 16 `p12 state`; 34 `input_offset += 8` | write fresh state |
| `ab_tail` | 36-39 `remaining`, `Bytes.blit input !input_offset buffer 0 remaining`, `buffered := remaining` | write fresh buffer |
| `ab_ret` | 40 `{ state; buffer; buffered }` returned | publish |
| `fs_copy` | 45 `let state = State.copy context.state` | allocate |
| `fs_xor_data` | 46-48 `x0 <- x0 xor load_partial_le context.buffer 0 context.buffered` | read published buffer, write fresh state |
| `fs_xor_pad` | 49 `x0 <- x0 xor padding context.buffered` (endian.ml:26-28) | write fresh state |
| `fs_p12` | 50-51 `p12 state` | write fresh state |
| `sos_copy` | 42 `squeezing_of_state`: `State.copy state`, `offset = 0` (via `finish`, 53); publish for `finish`, continue to `sq_copy` for `get` (ascon.ml:188-189) | allocate |
| `os_copy` | 7 `of_state`: `State.copy state` (ascon.ml:243) | allocate |
| `os_make` | 7 `Bytes.make 8 '\000'`, `buffered = 0`; return | allocate, publish |
| `sq_copy` | 58-59 `State.copy context.state`, `offset` | read published state, allocate |
| `sq_create` | 60-61 `Bytes.create length`, `written := 0` | allocate (uninitialised) |
| `sq_loop` | 62 `while !written < length` | — |
| `sq_lazy_p12` | *lazy variant only* (`Lazy = TRUE`): `if !offset = 8 then (p12 state; offset := 0)` at the start of an iteration | write fresh state |
| `sq_take` | 63 `take = min (8 - !offset) (length - !written)` | — |
| `sq_for` | 64-70, one step per iteration: `Bytes.unsafe_set output (!written + i)` byte `!offset + i` of `x0` | read fresh state, write fresh output |
| `sq_adv` | 71-73 `written +=`, `offset +=`, `if !offset = 8` (eager only) | — |
| `sq_p12` | 74-75 `p12 state; offset := 0` (eager variant = the real code) | write fresh state |
| `sq_ret` | 77 `({ state; offset }, output)`; `get` discards the context (ascon.ml:189 `snd`) | publish |

### 1.4 Abstract specification

An absorbing context *means* `(pre, m)`: the mask history before the message
(`<<0>>`, the IV permutation, for Hash/XOF; longer after `reinit`) and the
concatenation `m` of all chunks absorbed along its history.  A squeezing
context means `(fin, p)`: `fin = pre ++ blocks(pad(m))` with
`pad(m) = m ‖ 0x01 ‖ 0*` up to a multiple of `Rate` (a message whose length is a
multiple of `Rate` gets a full extra padding block), each block followed by one
`p12`; `p` is the number of output bytes already emitted.  Output byte `q` of
the stream is byte `q mod Rate` of `x0` after `q div Rate` further
permutations (`SpecOut`).  The minimum number of squeeze-phase permutations
needed to emit bytes `0..p-1` is `NeedSq(p) = max(0, ceil(p/Rate) - 1)`: only
the permutations *between* emitted blocks.

### 1.5 Properties

"Holds" means: checked by TLC in every pass configuration in which it is
listed, with no error.  The invariant names are those in `Sponge.tla`.

| Id | Property | Meaning | Result |
| --- | --- | --- | --- |
| a | `BufferedRange`, `OffsetRange` | every held absorbing context has `0 <= buffered < Rate`; every held squeezing context `0 <= offset < Rate` (lazy variant: `<= Rate`) | holds |
| a | `BufferContents` | `buffer` has `Rate` bytes, `buffered = len(m) mod Rate`, and `buffer[0..buffered)` is exactly the trailing `len(m) mod Rate` bytes of `m` (bytes beyond `buffered` are stale and unconstrained) | holds |
| b | `AbsorbRefinement` | the state object of every held absorbing context equals `(pre ++ fullblocks(m), 0)` | holds |
| b | `SqueezeRefinement` | the state and offset of every held squeezing context equal the representation of `(fin, p)` | holds |
| b | `OutputCorrect` | every `squeeze`/`get` output equals `SpecOut(fin, p) .. SpecOut(fin, p+L-1)`; no uninitialised byte is ever returned | holds |
| b | `SqueezeConcat` | for outputs produced in one behaviour, `squeeze a` then `squeeze b` from the result = `squeeze (a+b)` | holds (and reached, see witnesses) |
| b | `ZeroSqueezeNoop` | a zero-length squeeze returns no bytes, performs no permutation and returns a context equal by value to its input | holds |
| b | `AbsorbLoopInv`, `SqueezeLoopInv` | loop invariants at `sponge.ml:32` and `:62`; the squeeze one also gives progress (`offset < Rate` at the loop head) | holds |
| — | `Termination` | every operation of every domain terminates (checked in `Sponge_rate2` and both AEAD configurations, under weak fairness) | holds |
| c | `AbsorbPermMinimal` | an absorbing context has performed exactly `len(pre) + floor(len(m) / Rate)` permutations (one per absorbed block) | holds |
| c | `EagerExtraPermExact` | a squeezing context at position `p` has performed exactly `NeedSq(p) + [p > 0 and p mod Rate = 0]` squeeze permutations, and every `get` performs exactly `1 + DigestBlocks` | **holds — i.e. one permutation more than necessary** |
| c | `PermMinimal`, `OpPermMinimal`, `HashGetMinimal` | squeezing contexts / every `squeeze` call / every `get` perform only the minimum number of permutations | **VIOLATED by the real (eager) code** (finding F1); hold for the lazy variant |
| d | `Persistence` | the deep value of every context ever returned to the user never changes | holds |
| d | `NoWriteToPublished` | no step writes an object reachable from a returned context | holds |
| d | `NoUserAliasing` | no returned context references a user-owned `bytes` (inputs, returned outputs), and the library never writes one | holds |
| d, e | `WritesOnlyFresh` | every write of an operation targets an object allocated by that same operation (ownership discipline) | holds |
| e | `RaceFree` | in every interleaved state, no domain has written an object that another domain may currently read or write | holds |
| e | result = sequential result | all refinement properties above in the two-domain configuration (the meaning of every result is computed from the meaning of its input only) | holds |

Why `RaceFree` as a state invariant suffices: a data race needs a write by
one domain and an access by another to the same object without
synchronisation.  Every written object stays in the writer's `wr` set until
the operation returns (the synchronised publication point), and the
footprint of an in-flight operation contains every object it can touch.  So a
racing pair would make `wr[d1] ∩ Footprint(d2)` non-empty in the state after
the later of the two accesses, in some interleaving, and TLC explores all of
them.

### 1.6 Findings

**F1 — the eager squeeze performs one permutation more than SP 800-232
needs whenever an output ends on a block boundary (performance only).**
`Sponge.squeeze` permutes as soon as `offset` reaches 8 (sponge.ml:73-75),
even when no further output is requested.  `EagerExtraPermExact` (holds)
pins down exactly when: a squeezing context at a non-zero multiple of 8
carries one prepaid permutation, and it is wasted if the context is never
squeezed again.  Consequences in the public API:

* `Hash256.get` / `Hash256.digest` (ascon.ml:187-191) squeeze exactly 32 bytes,
  so *every* hash performs 1 (final block) + 4 squeeze permutations, but only
  1 + 3 can influence the digest: the state after the fourth squeeze
  permutation is discarded (`snd`, ascon.ml:189).  SP 800-232 and the
  reference implementation permute only *between* output blocks.
  `Sponge_economy_get` (real rate 8, 32-byte digest) is the TLC
  counterexample: `HashGetMinimal` is violated with `nperm = 5` at `sq_ret`;
  the fifth permutation is state 61 (`sq_p12` after `written = 32`), see
  below.  For a message shorter than 8 bytes this is 6 p12 calls (IV, final block,
  4 squeeze) instead of 5, i.e. one sixth of the permutation work of a
  short-message hash is wasted; the share shrinks with message length.
* `Xof128.digest` / `Cxof128.digest` with `length` a multiple of 8, and every
  incremental `squeeze` whose end position is a multiple of 8, perform one
  permutation that is only useful if the caller squeezes again
  (`Sponge_economy_squeeze`, `PermMinimal` violated after
  `finish; squeeze 8`).
* Outputs are *not* affected: `OutputCorrect`, `SqueezeRefinement` and
  `SqueezeConcat` hold for the eager code.

The **lazy variant** (`Lazy = TRUE`: permute at the start of the next block;
`offset = 8` means "block exhausted") refines the same output stream and
satisfies `PermMinimal`, `OpPermMinimal` and `HashGetMinimal`
(`Sponge_lazy`, `Sponge_lazy_rate8`).  Trade-off: with persistent contexts,
if a context at a block boundary is continued in several branches, the lazy
variant performs that permutation once per branch while the eager code
performed it once; for linear (single-shot or chained) use the lazy variant
is minimal.  If adopted, `SECURITY_REVIEW.md` ("records an offset from 0 to 7
... permute after each complete output block") would need updating.

Counterexample for `HashGetMinimal` (`./run.sh --expected-failures`, abridged
to the permutation-relevant states):

```
State  action       offset  written  nperm      (TLC: "State n: <action that produced it>")
  1    Initial      0       0        0          get on the empty message (Rate 8)
  6    fs_p12       0       0        1          sponge.ml:50  final-block permutation
 20    sq_for       0       0        1          ... 8 output bytes written (sponge.ml:66)
 21    sq_adv       8       8        1
 22    sq_p12       0       8        2          sponge.ml:74  between blocks 0 and 1 (needed)
 35    sq_p12       0       16       3          between blocks 1 and 2 (needed)
 48    sq_p12       0       24       4          between blocks 2 and 3 (needed)
 60    sq_adv       8       32       4          all 32 digest bytes already written
 61    sq_p12       0       32       5          sponge.ml:74  NOT needed: result discarded by `snd` (ascon.ml:189)
 63    sq_ret       0       32       5          HashGetMinimal: nperm = 5 /= 1 + (4 - 1)
```

**F2 — no correctness discrepancy found.**  Within the checked bounds the
code refines the SP 800-232 byte-oriented sponge (padding position, full
extra padding block, partial-block buffering across calls, stale buffer bytes
never absorbed, offset bookkeeping across squeeze calls, zero-length
squeezes), all returned contexts are persistent, and there are no data races
between domains that share contexts.  The documentation claims
(ascon.mli:93 "`get ctx` returns the digest without changing `ctx`",
ascon.mli:125-126 "Repeated calls concatenate to the same output as one longer
call", README "a zero-length incremental squeeze is a harmless no-op",
"Hash and XOF contexts are persistent") are confirmed by `Persistence`,
`SqueezeConcat`/`OutputCorrect` and `ZeroSqueezeNoop`.

**F3 — caveat (not checked by TLC): "immutable" contexts are not safe to
publish racily.**  ascon.mli:78, 105, 108, 135 and 138 call the contexts *immutable*.  They
are persistent, but each is built by *mutating* freshly allocated objects
after allocation (`Bytes.blit`, `state.x0 <- ...`, `p12`).  Under the OCaml 5
memory model only initialising writes are guaranteed visible to a domain that
obtains the pointer through a data race; the later non-atomic writes are not.
A context handed to another domain through an unsynchronised mutable field
could therefore be observed with a stale buffer or pre-permutation state
(wrong output, not memory unsafety).  The model assumes synchronised hand-off
(sequentially consistent interleavings), under which `RaceFree` holds.  This
is the usual OCaml 5 rule for any structure containing `bytes`/mutable
records; the documentation could say so explicitly.

**F4 — minor, allocation only.**  `finish` copies the state twice
(sponge.ml:45 and 42) and `Hash256.get` copies it a third time in `squeeze`
(sponge.ml:58).  The ownership analysis shows the second and third copies are
of objects that are not yet shared, so they are unnecessary for persistence;
they are harmless.

### 1.7 Mutation testing

Each mutant is a patched copy of `Sponge.tla` (PlusCal edited, then
re-translated) created and checked **outside the repository**.  Each mutant
was model-checked once per invariant (so the table lists *every* invariant
that catches it, not just the first) and once with all invariants.  Mutant
configurations: "seq" = one domain, Rate 2, 3 operations, distinct-symbol
bytes, absorb lengths 0..4, squeeze lengths 0..3; "conc" = two domains with
one operation each.  Numbers are the length (in states) of TLC's shortest
counterexample, seq/conc.  `PermBound` (at most 12 permutations per state
object) is used as a state constraint so that a diverging mutant stays
finite.  Mutants (i)-(iv) are the ones requested; S5-S8 are extra.

| Mutant | Bug reintroduced | Caught by (counterexample length, seq/conc) | First violation reported with all invariants |
| --- | --- | --- | --- |
| S1 (i) | `absorb` without `State.copy` (sponge.ml:19): mutates `context.state` in place | `Persistence` 7/7, `NoWriteToPublished` 7/7, `WritesOnlyFresh` 7/7, `RaceFree` –/8, `AbsorbRefinement` 7/7, `AbsorbPermMinimal` 8/8, `AbsorbLoopInv` 15/11, `SqueezeRefinement` 17/13, `EagerExtraPermExact` 17/14, `SqueezeLoopInv` 19/15, `OutputCorrect` 27/45 | `AbsorbRefinement` (7) |
| S2a (ii) | off-by-one `take = min (8 - !buffered - 1) ...` (sponge.ml:25) | `AbsorbLoopInv` 13, `BufferContents` 16, `AbsorbRefinement` 16, `AbsorbPermMinimal` 16, `SqueezeRefinement` 22, `EagerExtraPermExact` 22, `SqueezeLoopInv` 24, `OutputCorrect` 54 | `AbsorbLoopInv` (13) |
| S2b (ii) | off-by-one `take = min (8 - !buffered + 1) ...` (sponge.ml:25) | the `Bytes.blit` bounds assertion at `ab_blit1` (12) in every run: the mutated OCaml raises `Invalid_argument` out of `absorb` | assertion (12) |
| S2c (ii) | `buffered := remaining` executed unconditionally, outside `if remaining <> 0` (sponge.ml:37-39): a partial fill is forgotten | `BufferContents` 16, `AbsorbLoopInv` 20, `SqueezeRefinement` 22, `AbsorbRefinement` 23, `AbsorbPermMinimal` 23, `SqueezeLoopInv` 24, `OutputCorrect` 54 | `BufferContents` (16) |
| S3 (iii) | padding XORed at position `buffered + 1` (sponge.ml:49) | `SqueezeRefinement` 7, `AbsorbRefinement` 8 (via `reinit`), `SqueezeLoopInv` 9; in the other runs the `padding` range assertion (endian.ml:27 `invalid_arg`) at depth 11 | `SqueezeRefinement` (7) |
| S4 (iv) | `squeeze` permutes but does not reset `offset := 0` (sponge.ml:75); spins forever when more output is requested | `SqueezeLoopInv` 16, `OffsetRange` 19, `SqueezeRefinement` 19 | `SqueezeLoopInv` (16) |
| S5 | `absorb` without `Bytes.copy` of the buffer (sponge.ml:20) | `Persistence` 7/7, `NoWriteToPublished` 7/7, `WritesOnlyFresh` 7/7, `RaceFree` –/8, `BufferContents` 14/14, `AbsorbLoopInv` 20, `SqueezeRefinement` 21, `AbsorbRefinement` 22, `SqueezeLoopInv` 23, `OutputCorrect` 53 | `Persistence` (7) |
| S6 | `squeeze` without `State.copy` (sponge.ml:58) | `SqueezeRefinement` 17/17, `Persistence` 17/17, `NoWriteToPublished` 17/17, `WritesOnlyFresh` 17/17, `EagerExtraPermExact` 17/17, `SqueezeLoopInv` 22, `OutputCorrect` 29; `RaceFree` 18 in the real `Sponge_concurrent` configuration (needs two operations per domain) | `SqueezeRefinement` (17) |
| S7 | `finish_state` loads all 8 buffer bytes, i.e. absorbs the stale tail (sponge.ml:48) | `SqueezeRefinement` 24, `AbsorbRefinement` 25, `SqueezeLoopInv` 26, `OutputCorrect` 56 | `SqueezeRefinement` (24) |
| S8 | `finish_state` without `State.copy` (sponge.ml:45) | `NoWriteToPublished` 4/4, `WritesOnlyFresh` 4/4, `Persistence` 5/5, `RaceFree` –/5, `AbsorbRefinement` 5/5, `AbsorbPermMinimal` 6/6, `AbsorbLoopInv` 11/9, `SqueezeRefinement` 13/11, `EagerExtraPermExact` 14/12, `SqueezeLoopInv` 15/13, `OutputCorrect` 23/43 | `NoWriteToPublished` (4) |

Every mutant is caught.  Invariants that do not appear for a mutant were
checked and are not violated by it (e.g. the pure logic bugs S2-S4, S7 do
not break persistence; `RaceFree` is vacuous with one domain).
`TypeOK`, `BufferedRange`, `NoUserAliasing`, `SqueezeConcat` and
`ZeroSqueezeNoop` caught none of these mutants: they are implied by, or
weaker than, the refinement invariants for these bugs.

---

## 2. `AeadDecrypt.tla`

### 2.1 What is modelled

One call per behaviour, chosen by an adversary:

* `decrypt ~ciphertext ~tag` with any ciphertext length in `CtLens` (every
  length up to two full blocks plus every tail length, so both the
  `remaining >= 8` and `remaining < 8` branches) and a tag of any length in
  `TagLens` (short, exact, long) with arbitrary content;
* `decrypt_combined` with arbitrary content of every length in `CombLens`
  (shorter than the tag, exactly the tag, and longer);
* `Constant_time.equal` alone on every pair of byte strings of lengths
  `EqLens` over `EqVals` (including unequal lengths).

Abstractions: the AEAD rate is `2 * Word` (real 16 = 2 × 8) and the tag
`TagSize` bytes (real 16; model 2 and 3).  The expected tag is an
uninterpreted function of `(key, nonce, ad, ciphertext)`: since each
behaviour makes one call, choosing its value nondeterministically at
`finalize` quantifies over all such functions.  The keystream byte for rate
position `r` after ciphertext prefix `s` is the free atom `<<"ks", s, r>>`, so
`OkPlaintextCorrect` checks that every plaintext byte is
`keystream XOR ciphertext` for the right block and position and that no
`Bytes.create` byte leaks.  `initialize`, `absorb_associated_data`, the
padding and `replace_low_bytes` state updates and `finalize` are single
abstract steps (their bit-level correctness is covered by the KATs, not
here).  A ghost `events` trace records the processing steps.

| Label | OCaml (lib/ascon.ml unless noted) |
| --- | --- |
| `start` | adversary / caller chooses the entry point and arguments |
| `dc_len` | 169-170 `if length < tag_size then Error Invalid_tag_length` |
| `dc_sub_ct` | 172-173 `Bytes.sub combined 0 ciphertext_length` |
| `dc_sub_tag` | 174 `Bytes.sub combined ciphertext_length tag_size`; 175 calls `decrypt` |
| `d_check` | 117 `if Bytes.length tag <> tag_size then Error Invalid_tag_length` |
| `d_init` | 119 `initialize key nonce` |
| `d_ad` | 120 `absorb_associated_data` (incl. domain separation, 68-70) |
| `d_alloc` | 121-123 `length`, `Bytes.create length`, `offset := 0` |
| `d_loop` | 124 `while length - !offset >= 16` |
| `d_blk_lo` / `d_blk_hi` | 125-128 the two `store64_le plaintext ...` |
| `d_blk_st` | 129-132 `x0 <- c0; x1 <- c1; p8; offset += 16` |
| `d_tail` | 134-135 `remaining`, `if remaining >= 8` |
| `d_tA_lo` / `d_tA_hi` / `d_tA_st` | 136-139 / 137-141 / 142-144 (tail of at least 8 bytes) |
| `d_tB` / `d_tB_st` | 146-148 / 149-150 (tail shorter than 8 bytes) |
| `d_final` | 151 `let expected_tag = finalize state k0 k1` |
| `d_cmp` | 152 `Constant_time.equal expected_tag tag` |
| `ct_len`, `ct_loop`, `ct_ret` | constant_time.ml 2-3, 5-10 (one step per iteration), 11 |
| `d_branch` | 152 `then Ok plaintext` |
| `d_fill` | 155 `Bytes.fill plaintext 0 length '\000'` |
| `d_fail` | 156 `Error Authentication_failure` |

### 2.2 Properties (all hold)

| Property | Meaning |
| --- | --- |
| `TagLenCheckedFirst` | the tag-length check is the first step of `decrypt` |
| `BadTagLenRejectedEarly` | a tag of the wrong length yields `Invalid_tag_length` with no `initialize`, no AD absorption, no allocation, no comparison |
| `InvalidLenOnlyIfBadLen` | `Invalid_tag_length` is only returned for a wrong tag length (or a combined input shorter than the tag) |
| `ReleaseOnlyIfTagValid` | `Ok` only if the provided tag has exactly `TagSize` bytes and equals the full expected tag |
| `RejectOnlyIfTagInvalid` | `Authentication_failure` only if the tags differ (no false rejection) |
| `OkPlaintextCorrect` | the released plaintext is the fully initialised SP 800-232 decryption |
| `FailureZeroFilled` | on failure the candidate buffer is all zero and the zero-fill precedes the return |
| `NoPartialRelease` | the candidate buffer is reachable by the caller only after an `Ok` return |
| `CompareBeforeOutcome` | both outcomes happen after finalisation and the comparison |
| `CtEqualCorrect` | `Constant_time.equal a b = (a = b)`, for all lengths |
| `CtEqualNoEarlyExit` | for equal lengths exactly `len` iterations reading indices `0..len-1` in order whatever the contents; unequal lengths return `false` after 0 iterations |
| `CombinedShortRejected` | `decrypt_combined` of fewer than `TagSize` bytes returns `Invalid_tag_length` without splitting or processing |
| `CombinedSplit` | otherwise `ciphertext ‖ tag = combined` with a `TagSize`-byte tag, so `Invalid_tag_length` can never follow |
| `Termination` | every call terminates |

`CtEqualNoEarlyExit` shows that the *iteration count and index sequence* of
the OCaml source are functions of the lengths only (the lengths are public).
It says nothing about the code the compiler emits or the CPU's timing,
consistent with README "No formal constant-time claim is made".

AEAD_Each mutant is a patched copy of `Sponge.tla` (PlusCal edited, then
re-translated) created and checked **outside the repository**.  Each mutant
was model-checked once per invariant (so the table lists *every* invariant
that catches it, not just the first) and once with all invariants.  Mutant
configurations: "seq" = one domain, Rate 2, 3 operations, distinct-symbol
bytes, absorb lengths 0..4, squeeze lengths 0..3; "conc" = two domains with
one operation each.  Numbers are the length (in states) of TLC's shortest
counterexample, seq/conc.  `PermBound` (at most 12 permutations per state
object) is used as a state constraint so that a diverging mutant stays
finite.  Mutants (i)-(iv) are the ones requested; S5-S8 are extra.

| Mutant | Bug reintroduced | Caught by (counterexample length, seq/conc) | First violation reported with all invariants |
| --- | --- | --- | --- |
| S1 (i) | `absorb` without `State.copy` (sponge.ml:19): mutates `context.state` in place | `Persistence` 7/7, `NoWriteToPublished` 7/7, `WritesOnlyFresh` 7/7, `RaceFree` –/8, `AbsorbRefinement` 7/7, `AbsorbPermMinimal` 8/8, `AbsorbLoopInv` 15/11, `SqueezeRefinement` 17/13, `EagerExtraPermExact` 17/14, `SqueezeLoopInv` 19/15, `OutputCorrect` 27/45 | `AbsorbRefinement` (7) |
| S2a (ii) | off-by-one `take = min (8 - !buffered - 1) ...` (sponge.ml:25) | `AbsorbLoopInv` 13, `BufferContents` 16, `AbsorbRefinement` 16, `AbsorbPermMinimal` 16, `SqueezeRefinement` 22, `EagerExtraPermExact` 22, `SqueezeLoopInv` 24, `OutputCorrect` 54 | `AbsorbLoopInv` (13) |
| S2b (ii) | off-by-one `take = min (8 - !buffered + 1) ...` (sponge.ml:25) | the `Bytes.blit` bounds assertion at `ab_blit1` (12) in every run: the mutated OCaml raises `Invalid_argument` out of `absorb` | assertion (12) |
| S2c (ii) | `buffered := remaining` executed unconditionally, outside `if remaining <> 0` (sponge.ml:37-39): a partial fill is forgotten | `BufferContents` 16, `AbsorbLoopInv` 20, `SqueezeRefinement` 22, `AbsorbRefinement` 23, `AbsorbPermMinimal` 23, `SqueezeLoopInv` 24, `OutputCorrect` 54 | `BufferContents` (16) |
| S3 (iii) | padding XORed at position `buffered + 1` (sponge.ml:49) | `SqueezeRefinement` 7, `AbsorbRefinement` 8 (via `reinit`), `SqueezeLoopInv` 9; in the other runs the `padding` range assertion (endian.ml:27 `invalid_arg`) at depth 11 | `SqueezeRefinement` (7) |
| S4 (iv) | `squeeze` permutes but does not reset `offset := 0` (sponge.ml:75); spins forever when more output is requested | `SqueezeLoopInv` 16, `OffsetRange` 19, `SqueezeRefinement` 19 | `SqueezeLoopInv` (16) |
| S5 | `absorb` without `Bytes.copy` of the buffer (sponge.ml:20) | `Persistence` 7/7, `NoWriteToPublished` 7/7, `WritesOnlyFresh` 7/7, `RaceFree` –/8, `BufferContents` 14/14, `AbsorbLoopInv` 20, `SqueezeRefinement` 21, `AbsorbRefinement` 22, `SqueezeLoopInv` 23, `OutputCorrect` 53 | `Persistence` (7) |
| S6 | `squeeze` without `State.copy` (sponge.ml:58) | `SqueezeRefinement` 17/17, `Persistence` 17/17, `NoWriteToPublished` 17/17, `WritesOnlyFresh` 17/17, `EagerExtraPermExact` 17/17, `SqueezeLoopInv` 22, `OutputCorrect` 29; `RaceFree` 18 in the real `Sponge_concurrent` configuration (needs two operations per domain) | `SqueezeRefinement` (17) |
| S7 | `finish_state` loads all 8 buffer bytes, i.e. absorbs the stale tail (sponge.ml:48) | `SqueezeRefinement` 24, `AbsorbRefinement` 25, `SqueezeLoopInv` 26, `OutputCorrect` 56 | `SqueezeRefinement` (24) |
| S8 | `finish_state` without `State.copy` (sponge.ml:45) | `NoWriteToPublished` 4/4, `WritesOnlyFresh` 4/4, `Persistence` 5/5, `RaceFree` –/5, `AbsorbRefinement` 5/5, `AbsorbPermMinimal` 6/6, `AbsorbLoopInv` 11/9, `SqueezeRefinement` 13/11, `EagerExtraPermExact` 14/12, `SqueezeLoopInv` 15/13, `OutputCorrect` 23/43 | `NoWriteToPublished` (4) |

Every mutant is caught.  Invariants that do not appear for a mutant were
checked and are not violated by it (e.g. the pure logic bugs S2-S4, S7 do
not break persistence; `RaceFree` is vacuous with one domain).
`TypeOK`, `BufferedRange`, `NoUserAliasing`, `SqueezeConcat` and
`ZeroSqueezeNoop` caught none of these mutants: they are implied by, or
weaker than, the refinement invariants for these bugs.

---

## 3. What was not checked

* The permutation, S-box, round constants, `p8`/`p12` round selection, the
  AEAD state updates (`initialize`, AD padding and domain separation,
  `replace_low_bytes`, final-block padding) and tag computation — abstracted;
  they are covered by the KAT and differential tests, not by these models.
* Unbounded behaviours: all results are bounded model checking (operation
  counts, lengths and rates as in the tables).  Generalisation to Rate 8 and
  longer histories rests on the small-scope/data-independence argument of §1.2
  plus the direct Rate-8 runs.
* Weak-memory behaviours of racy OCaml 5 programs (F3): the model uses
  sequentially consistent interleavings with synchronised publication.
* Timing: only the source-level loop structure of `Constant_time.equal`; not
  compiled code, the GC, or hardware.
* Whether the zero-filled plaintext survives elsewhere in memory (the GC may
  have copied it; README calls the zero-fill best effort).
* Argument validation outside the modelled functions: `Sys.max_string_length`
  and negative lengths (sponge.ml:56-57, ascon.ml:161-162, 205-213,
  247-255), `Key`/`Nonce` length checks, the CXOF customization length limit
  and `Z0` length block (ascon.ml:226-236).
* Concurrent mutation of a user's input `bytes` by another domain while it is
  being absorbed (a data race in user code; the library never retains input
  or output buffers, which `NoUserAliasing` does check).
