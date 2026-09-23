# Formal verification of `ocaml-ascon`

This directory contains a machine-checked verification of the library in
`lib/` against NIST SP 800-232 (August 2025). It has two parts:

- [`lean/`](lean/) — **Lean 4 proofs of functional correctness.** Every
  function in `lib/` is transcribed into Lean statement by statement. For
  *all* inputs, the transcription is proved to compute exactly what an
  independent Lean transcription of SP 800-232 prescribes, and to do so with
  no exception, no out-of-bounds `unsafe_get`/`unsafe_set`, no read of
  uninitialized `Bytes.create` memory, and no `Int64` shift by an amount with
  unspecified behaviour.
- [`tla/`](tla/) — **TLA+ models checked with TLC.** These cover the parts
  that a functional model cannot express: the OCaml heap and aliasing
  (persistence of contexts), two OCaml 5 domains running on shared contexts,
  the incremental buffer/offset state machine, the number of permutations
  executed, and the AEAD rule that plaintext is released only after tag
  verification.

The findings and their fixes are listed [below](#findings).
`lib/internal/sponge.ml` includes the fix for finding 1, and both the Lean
proofs and the TLA+ models describe the fixed code.

## Results at a glance

| Property | How | Result |
| --- | --- | --- |
| Lean specification equals SP 800-232 as implemented by `ascon-c` | `lake exe kat`: all 4,228 official KAT vectors, `p[8]`/`p[12]` of zero, and the three Appendix B IV states, all evaluated on the *specification* | 4,228 / 4,228 |
| S-box table (Table 6) = bitsliced formula used by the code | Lean `Spec.pS_eq_pSBitsliced` | proved |
| `Permutation.rounds s n` = `Ascon-p[n]` for 1 ≤ n ≤ 12 | Lean `Permutation.rounds_correct` | proved |
| Little-endian loads/stores, padding, `replace_low_bytes` | Lean `Endian.*_ok` | proved |
| `Constant_time.equal a b` decides `a = b` | Lean `ConstantTime.equal_ok` | proved |
| Hash256: one-shot, and **every** chunking of `feed` | Lean `Hash256.digest_correct`, `Hash256.incremental_correct` | proved |
| XOF128: one-shot, and every absorb chunking followed by every sequence of `squeeze` lengths | Lean `Xof128.digest_correct`, `Xof128.streaming_correct` | proved |
| CXOF128, including the 256-byte customization limit | Lean `Cxof128.digest_correct`, `Cxof128.init_correct`, `Cxof128.init_too_long` | proved |
| AEAD128 encrypt / decrypt / combined forms = Algorithms 3 and 4 | Lean `Aead128.encrypt_correct`, `decrypt_correct`, `encryptCombined_correct`, `decryptCombined_correct` | proved |
| AEAD128 decryption inverts encryption | Lean `Spec.decrypt_encrypt`, `Aead128.decrypt_encrypt` | proved |
| OCaml library = Lean specification beyond the KAT ranges | `lean/differential.py`: 1,600 random and all-boundary cases | equal |
| Contexts are persistent: no returned context is ever modified | TLC `Persistence`, `NoWriteToPublished` | holds |
| No data races between two OCaml 5 domains sharing contexts | TLC `RaceFree` (2 domains × 2 operations) | holds |
| Plaintext only released after full-tag verification; rejected buffer zero-filled | TLC `AeadDecrypt` properties | holds |
| `Constant_time.equal` always runs `len` iterations | TLC `AeadDecrypt` | holds |
| No more permutations than SP 800-232 requires | TLC `PermMinimal`, `OpPermMinimal`, `HashGetMinimal` | holds (violated before the fix for finding 1) |

**No functional correctness bug was found.** For every input, the four
algorithms return the standardized outputs, and every guard inside the
library is proved never to fire on a public-API path.

## Findings

1. **Performance: `Sponge.squeeze` performed one permutation that SP 800-232
   does not need** whenever an output ended on an 8-byte block boundary.
   Every `Hash256.get`/`digest` paid it: 5 squeeze-side `p12` calls where 4
   are needed, so a short-message hash ran 6 permutations instead of 5.
   Outputs were unaffected. TLC found it (`Sponge_eager_economy_get`,
   `Sponge_eager_economy_squeeze`; see
   [`tla/README.md`](tla/README.md#16-findings), F1). *Fixed:* `squeeze`
   now permutes only when another output byte is needed. The Lean
   proofs (`Sponge.squeeze_correct` with the two-form `AtPos` invariant) and
   the TLA+ minimality properties hold for the new code. An empty-message
   Hash256 is about 16% faster and allocates 20% less.
2. **Undocumented exception: `Aead128.encrypt_combined` raises
   `Invalid_argument`** when `Bytes.length plaintext > Sys.max_string_length -
   16`. The Lean theorem `encryptCombined_correct` states the exact
   condition. The limit is unreachable on 64-bit runtimes, but on a 32-bit
   runtime it is a plaintext of about 16 MiB. `ascon.mli` does not mention
   the exception. *Documented in
   [#3](https://github.com/thevilledev/ocaml-ascon/pull/3).*
3. **Documentation: "immutable" contexts.** `ascon.mli` calls the hash and
   XOF contexts *immutable*. TLC proves them *persistent*, meaning no returned
   context is ever changed. Internally, however, each one is built by
   mutating freshly allocated objects, so under the OCaml 5 memory model it
   must be handed to another domain through synchronization and not a data
   race ([`tla/README.md`](tla/README.md#16-findings), F3). *Clarified in
   [#4](https://github.com/thevilledev/ocaml-ascon/pull/4).*
4. **Test tooling: the differential harness does not cover every rate
   boundary.** `tools/differential/run.py` is meant to exercise the boundary
   lengths first, but it samples them at random, so a typical run misses
   about a third of them. It also never exercises decryption. *Fixed in
   [#5](https://github.com/thevilledev/ocaml-ascon/pull/5).*

TLC also observed that `finish` and `Hash256.get` copy the state more often
than needed (tla F4). This only costs allocations and is left as is.

## Trusted base and limits

The guarantees depend on the following, which are not themselves verified:

- **The Lean model is a faithful transcription of the OCaml code.** It is
  hand-written, statement by statement, with the OCaml file and line
  given in each docstring. Two checks back this up: the model is *proved*
  equal to a specification that is validated against the official vectors,
  and `differential.py` compares the real OCaml library with that
  specification on 1,600 further cases.
- **The OCaml runtime model** ([`lean/Ascon/Model/Runtime.lean`](lean/Ascon/Model/Runtime.lean)):
  `int64` operations are two's-complement bit-vector operations, `bytes` is a
  list of possibly-uninitialized bytes, and `Sys.max_string_length` has its
  64-bit value. OCaml `int` is modelled by unbounded `Int`. That no library
  computation overflows is argued rather than mechanized: every intermediate
  value is at most an input length plus 16, and the proved invariants bound
  every offset by the input length.
- **Lean itself.** That is the kernel, plus, for `bv_decide`, the compiled
  LRAT checker: `#print axioms` lists `…_native.bv_decide.ax_*` next to
  `propext`, `Classical.choice` and `Quot.sound`. The KAT runner also trusts
  the Lean compiler. There are no `sorry`s.
- **TLC's bounds.** The TLA+ results are exhaustive only within the
  configured bounds (rates 2, 3 and 8, small alphabets, up to five
  operations). [`tla/README.md`](tla/README.md) explains why these bounds
  generalize for this code. The permutation is abstracted symbolically.
- **Not covered.** Timing of compiled code and hardware side channels
  (only the source-level loop structure of `Constant_time.equal` is
  checked). What the garbage collector retains. Weak-memory behaviour of
  *racy* programs. Arbitrary bit-length inputs, which the library does not
  accept.

## Running

Requirements: Lean 4 via [`elan`](https://github.com/leanprover/elan) (the
toolchain is pinned in `lean/lean-toolchain`; no Mathlib), Java 11+, and
`tla2tools.jar` 1.7.4. The differential test also needs the OCaml toolchain
used for the library.

```sh
cd formal/lean
lake build                              # check every proof (about 1 minute)
lake exe kat ../../test/vectors         # the spec against all official vectors
python3 differential.py --cases 400     # the OCaml library against the spec

cd ../tla
./run.sh                                # every TLC configuration that must pass
./run.sh --expected-failures            # the documented finding 1 counterexamples
```
