# ascon — NIST SP 800-232 in pure OCaml

`ascon` is a small, portable implementation of the final **NIST SP 800-232
(August 2025)** Ascon standard. It provides:

- `Ascon.Aead128` — authenticated encryption with associated data;
- `Ascon.Hash256` — a fixed 256-bit hash;
- `Ascon.Xof128` — an extendable-output function; and
- `Ascon.Cxof128` — a customized extendable-output function.

> **Version warning:** this is the standardized little-endian design. It is
> not Ascon v1.2 and is not byte-for-byte compatible with the older NIST LWC
> submission.

The core is pure OCaml, uses `Int64` for the five-word permutation state, has
no runtime dependencies beyond the OCaml standard library, and does not depend
on Unix or C. It is intended to work in ordinary Unix applications and
MirageOS-style environments.

## Status

The four mandatory SP 800-232 algorithms are implemented, documented, and
tested against the complete byte-oriented KAT files from the official
[`ascon/ascon-c`](https://github.com/ascon/ascon-c) repository. The current API
supports whole-byte inputs and outputs only. Tag truncation, nonce masking, and
incremental AEAD are intentionally deferred beyond the first release.

This software has **not** received an independent security audit and is **not**
a FIPS-validated or NIST-validated cryptographic module. Passing vectors is not
equivalent to either kind of review.

## Installation

Once published to opam:

```sh
opam install ascon
```

To use the current checkout:

```sh
opam pin add ascon.dev .
```

Add `(libraries ascon)` to the relevant dune stanza.

The supported compiler range begins at OCaml 4.14. CI covers OCaml 4.14 and
several current OCaml 5.x releases on Linux, plus current OCaml 5.x on macOS.

## Quick examples

### Hash256

```ocaml
let digest = Ascon.Hash256.digest_string "message"
(* [digest] is exactly 32 bytes. *)
```

Incremental hash contexts are immutable:

```ocaml
let context = Ascon.Hash256.init () in
let context = Ascon.Hash256.feed_string context "first chunk" in
let context = Ascon.Hash256.feed context (Bytes.of_string "second chunk") in
let digest = Ascon.Hash256.get context
```

### AEAD128

`key_bytes` must come from a suitable secure key source. `nonce_bytes` must be
unique for every encryption under that key.

```ocaml
let () =
  let key = Result.get_ok (Ascon.Aead128.Key.of_bytes key_bytes) in
  let nonce = Result.get_ok (Ascon.Aead128.Nonce.of_bytes nonce_bytes) in
  let associated_data = Bytes.of_string "record header" in
  let plaintext = Bytes.of_string "secret payload" in
  let ciphertext, tag =
    Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext
  in
  match Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext ~tag with
  | Ok authenticated_plaintext -> use authenticated_plaintext
  | Error `Authentication_failure -> reject_record ()
  | Error `Invalid_tag_length -> reject_malformed_record ()
```

Decryption buffers the complete candidate plaintext and returns it only after
successful verification of the full 128-bit tag. Combined `ciphertext || tag`
helpers are also available.

> **Never reuse a nonce with the same Ascon-AEAD128 key.** Nonce reuse breaks
> the scheme's security requirements.

### Incremental XOF128

The types enforce the `absorb* → squeeze*` lifecycle: a squeezing state cannot
be passed to `absorb`.

```ocaml
let () =
  let absorbing = Ascon.Xof128.init () in
  let absorbing = Ascon.Xof128.absorb absorbing (Bytes.of_string "first ") in
  let absorbing = Ascon.Xof128.absorb absorbing (Bytes.of_string "second") in
  let squeezing = Ascon.Xof128.start_squeezing absorbing in
  let squeezing, first =
    Result.get_ok (Ascon.Xof128.squeeze squeezing ~length:17)
  in
  let _squeezing, next =
    Result.get_ok (Ascon.Xof128.squeeze squeezing ~length:15)
  in
  assert (Bytes.length first + Bytes.length next = 32)
```

Repeated squeeze calls produce consecutive output; their concatenation equals
one long squeeze from an equivalent state. One-shot XOF and CXOF output lengths
must be positive; a zero-length incremental squeeze is a harmless no-op.

### Customized XOF128

Customization strings provide explicit domain separation and are limited by
the standard to 256 bytes:

```ocaml
let () =
  let output =
    Ascon.Cxof128.digest
      ~customization:(Bytes.of_string "com.example.protocol/transcript-v1")
      ~message:(Bytes.of_string "message")
      ~length:32
  in
  match output with
  | Ok bytes -> use bytes
  | Error `Customization_too_long -> reject_configuration ()
  | Error `Invalid_length -> assert false
```

See the four complete programs in [`examples/`](examples/).

## Architecture

The public surface is a single `Ascon` module. The raw permutation is not part
of the installed public API.

```text
lib/ascon.{ml,mli}          explicit public constructions and typed APIs
lib/internal/state.*        mutable five-word 320-bit state
lib/internal/endian.*       portable little-endian loads, stores, and padding
lib/internal/permutation.*  shared p[12]/p[8] round implementation
lib/internal/sponge.*       persistent 64-bit-rate absorb/squeeze machinery
lib/internal/constant_time.* full-scan authentication-tag comparison
```

Hash and XOF contexts are persistent: each update copies the small state and
buffer. This makes branching and reuse unsurprising at the cost of allocation.
AEAD is intentionally one-shot so unauthenticated plaintext is never released.

## Building and testing

```sh
dune build
dune runtest --no-buffer
dune build @doc
dune exec examples/hash256.exe
dune exec examples/xof128.exe
dune exec examples/cxof128.exe
dune exec examples/aead128.exe
```

The normal test run covers:

- independent little-endian load/store and padding tests;
- independently sourced `p[8]` and `p[12]` state outputs;
- NIST's precomputed Hash/XOF/CXOF initialization states;
- all 1,089 AEAD, 1,025 Hash256, 1,025 XOF128, and 1,089 CXOF128 official
  vectors — 4,228 vectors in total;
- all important rate boundaries from 0 through 65 bytes;
- incremental chunking and multi-call squeezing equivalence;
- authentication failure after ciphertext, tag, associated-data, or nonce
  modification; and
- 250 reproducible property-test cases.

The vendored vectors are copied byte-for-byte from `ascon/ascon-c` commit
`446347f21b209f3921c65ece70027c366cbe1693`, with CC0 license and attribution
under [`test/vectors/`](test/vectors/). Old Ascon v1.2 vectors are not present.

An optional developer harness performs randomized differential comparison with
an external official C checkout:

```sh
python3 tools/differential/run.py /path/to/ascon-c --cases 100
```

The C code is built in a temporary directory and is never a package dependency.

## Benchmarks

Run the complete matrix with:

```sh
dune exec --profile release bench/bench_ascon.exe
```

An illustrative run on Apple ARM64, macOS 26.6, OCaml 5.5.0, using the dune
release profile produced:

| Operation | 1 KiB | 1 MiB | Allocated words/op at 1 KiB |
| --- | ---: | ---: | ---: |
| AEAD128 encrypt | 47.4 MB/s | 51.0 MB/s | 15,898 |
| AEAD128 decrypt | 48.4 MB/s | 42.4 MB/s | 15,898 |
| Hash256 | 18.8 MB/s | 19.9 MB/s | 44,254 |
| XOF128, 32-byte output | 19.2 MB/s | 18.6 MB/s | 44,254 |
| CXOF128, 32-byte output | 17.2 MB/s | 19.2 MB/s | 45,295 |

`Ascon-p[12]` measured 447 ns per permutation (2.24 million permutations per
second). These are baseline implementation numbers, not promises; compare only
results measured on the same machine. The benchmark also reports 0, 8, 16, 32,
64, 256, 4,096, and 16,384-byte sizes, nanoseconds per operation, throughput,
and allocation.

## Security notes

- Authentication-tag comparison scans every byte without content-dependent
  early exit. No formal constant-time claim is made for generated code, the
  compiler, or the OCaml runtime.
- OCaml heap data cannot be reliably zeroized. The garbage collector may copy
  or retain keys and plaintext. A rejected candidate plaintext is overwritten
  on a best-effort basis, but this is not a zeroization guarantee.
- Keys and nonces are copied into abstract validated 16-byte values; incorrect
  lengths are never truncated.
- Ordinary authentication failure is returned as a typed error, not raised as
  an exception.
- This release supports full 128-bit AEAD tags only.
- The API does not claim arbitrary bitstring support.

See [`SECURITY.md`](SECURITY.md) for reporting and support policy and
[`SECURITY_REVIEW.md`](SECURITY_REVIEW.md) for the implementation checklist.

## References and license

- [NIST SP 800-232, final August 2025](https://doi.org/10.6028/NIST.SP.800-232)
- [Official Ascon C implementations and vectors](https://github.com/ascon/ascon-c)

The OCaml implementation is ISC-licensed. The vendored official vectors are
CC0 1.0 Universal, as documented in their directory.
