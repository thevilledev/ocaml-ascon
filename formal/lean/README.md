# Lean 4 proofs

The development has three layers. Each depends only on the layers above it.

| Layer | Directory | Content |
| --- | --- | --- |
| Specification | `Ascon/Spec/` | SP 800-232 for byte-aligned inputs: the permutation with the S-box *table*, `parse`, `pad`, and Algorithms 3–7. It is written from the standard and never refers to the implementation. |
| Implementation model | `Ascon/Model/` | A statement-by-statement transcription of `lib/internal/*.ml` and `lib/ascon.ml` on top of a model of the OCaml runtime (`Runtime.lean`). |
| Proofs | `Ascon/Proofs/` | The model computes the specification for every input and never faults. |

`Kat.lean` evaluates the specification on the official vector files.
`SpecDriver.lean` and `differential.py` compare the specification with the
real OCaml library.

## Main theorems

All are in namespace `Ascon.Model` unless marked `Spec`.
`Bytes.ofList l` is an OCaml `bytes` value holding the initialized bytes `l`.

| Theorem | Statement (informal) |
| --- | --- |
| `Spec.pS_eq_pSBitsliced` | The table-based substitution layer equals the bitsliced formula (SP 800-232, Fig. 3). |
| `Permutation.rounds_correct` | For `1 ≤ n ≤ 12`, `rounds s n = .ok (Ascon-p[n] s)`. |
| `Permutation.rounds_invalid` | Other round counts raise `Invalid_argument`. |
| `Endian.loadPartialLe_ok`, `storePartialLe_ok`, `padding_ok`, `replaceLowBytes_ok` | The little-endian helpers compute the intended values, and their guards do not fire. |
| `ConstantTime.equal_ok` | `equal a b = .ok (decide (a = b))`. |
| `Sponge.absorb_correct` | If a context stands for message `m`, then `absorb` on `x` succeeds and gives a context that stands for `m ++ x`. Buffer and `0 ≤ buffered < 8` invariants included. |
| `Sponge.finishState_correct` | Finalization absorbs `pad(final block)`. |
| `Sponge.squeeze_correct` | `squeeze` returns the next `L` bytes of the output stream, advances the position by `L`, and initializes every output byte. The squeeze loop terminates. A context at a used-up block boundary may defer its permutation (`offset = 8`; see `AtPos`). |
| `Hash256.digest_correct`, `Hash256.incremental_correct` | `digest M` is Ascon-Hash256(M), and `init`, then `feed` on any chunks, then `get` gives the hash of their concatenation. |
| `Xof128.digest_correct`, `Xof128.streaming_correct`, `Xof128.squeeze_invalid` | One-shot XOF for every valid length, else `Invalid_length`. Any absorb chunking followed by any sequence of squeeze lengths yields the one-shot output of the total length. |
| `Cxof128.digest_correct`, `Cxof128.init_correct`, `Cxof128.init_too_long` | Ascon-CXOF128, including `Z₀` and the 256-byte limit. |
| `Aead128.encrypt_correct` | `encrypt` returns exactly `Ascon-AEAD128.enc(K, N, A, P)`. |
| `Aead128.decrypt_correct` | `decrypt` returns exactly `Ascon-AEAD128.dec(K, N, A, C, T)`, including `Invalid_tag_length` for tags other than 16 bytes. |
| `Aead128.encryptCombined_correct`, `decryptCombined_correct` | The combined format is `C ‖ T`. `encrypt_combined` raises `Invalid_argument` iff `‖P‖ > Sys.max_string_length − 16`. |
| `Spec.decrypt_encrypt`, `Aead128.decrypt_encrypt` | Decryption inverts encryption, for the specification and for the model. |

Every `*_correct` statement has the form `model inputs = .ok (spec inputs)`.
The monad `M` is `Except Fault`, so each theorem also proves that the OCaml
code raises no exception and performs no operation with undefined or
unspecified behaviour on that path.

## Modelling decisions

- **Faults.** `invalid_arg` (and therefore every internal guard),
  out-of-bounds `Bytes.unsafe_get`/`unsafe_set` and `Array.unsafe_get`, reads
  of bytes that `Bytes.create` left uninitialized, `Int64` shifts outside
  `[0, 63]`, and `Char.chr` outside `[0, 255]` all produce a `Fault` instead of
  a value.
- **Mutable state.** `State.t` is a value, and each field assignment is a
  record update. Aliasing between heap objects, and hence persistence and
  concurrency, is checked in the TLA+ model instead.
- **Loops.** `for` loops use `forUp`, and each `while` loop is a recursive
  function with a termination measure. The `squeeze` loop carries an explicit
  iteration budget, and exhausting it is the fault `loopBound`, so the
  correctness theorem also proves termination.
- **Factoring.** `Sponge.absorb` is split along its three code regions
  (`fillPending`, `absorbLoop`, `keepRemainder`). The same goes for the final
  block of each AEAD phase (`adTail`, `encryptTail`, `decryptTail`) and for
  `Cxof128.init` (`customizedState`). Each helper's docstring names the lines
  it transcribes.
- **Fast evaluation.** Executing the table-based S-box is slow. A
  `@[csimp]` lemma, justified by `pS_eq_pSBitsliced`, makes compiled code use
  the bitsliced form. Definitions and proofs still refer to the table.
- **Kernel performance.** Several proofs rewrite with `bind_of_ok`/`ok_bind`
  and `generalize` the permuted state rather than unfolding `bind`. This
  keeps the kernel's definitional-equality checks from evaluating
  `Ascon-p[12]` symbolically.
