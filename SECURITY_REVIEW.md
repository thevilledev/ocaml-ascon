# SP 800-232 implementation review checklist

This is a focused implementation self-review, not an independent audit. Each
item should be rechecked by a human reviewer before v0.1.0.

## Representation and permutation

- **SP 800-232 versus v1.2 endianness:** every external word is loaded and
  stored byte-by-byte in explicit little-endian order. Tests map
  `01 23 45 67 89 ab cd ef` to `0xefcdab8967452301`. No host-endian casts or
  big-endian compatibility helpers exist.
- **Round constants:** the shared schedule is `f0 e1 d2 c3 b4 a5 96 87 78 69
  5a 4b`, XORed into the low byte of `S2`.
- **Rotation constants:** diffusion uses `(19,28)`, `(61,39)`, `(1,6)`,
  `(10,17)`, and `(7,41)` for `S0` through `S4`, respectively.
- **Round selection:** `p[12]` uses all rounds; `p[8]` starts at `b4`. The same
  round function implements both.
- **Independent validation:** zero-state `p[8]` and `p[12]` outputs came from
  the official C reference. NIST Appendix B's three precomputed hash/XOF/CXOF
  initialization states are also checked.
- **Architecture portability:** the core uses only specified-width `Int64`
  shifts and bitwise operations plus byte access. It does not convert through
  native-width integers except for bounded byte values, offsets, and lengths.

## Padding, domains, and rates

- **IV constants:** AEAD128 `0x00001000808c0001`, Hash256
  `0x0000080100cc0002`, XOF128 `0x0000080000cc0003`, and CXOF128
  `0x0000080000cc0004` match final SP 800-232.
- **Padding:** byte-aligned padding XORs `0x01` at the first unused byte. A
  message ending on a rate boundary receives a separate empty padded block.
- **Domain separation:** AEAD XORs bit 319 (`0x8000000000000000` in `S4`) after
  the associated-data phase, including when associated data is empty.
- **Rates:** AEAD associated data and payload use 16-byte blocks with `p[8]`.
  Hash256, XOF128, and CXOF128 use 8-byte blocks with `p[12]`.
- **Associated-data empty/non-empty behavior:** an empty string skips its
  padding/permutation phase; every non-empty string is parsed and padded before
  domain separation. Official vectors cover both.
- **CXOF customization:** the bit length is XORed as a 64-bit little-endian
  integer and permuted, then customization and message are independently
  parsed and padded. The 256-byte maximum is enforced; 257 bytes is rejected.

## AEAD payload and authentication

- **Final partial block:** encryption emits only the occupied rate bytes before
  applying padding. Decryption replaces only received low bytes in the state,
  preserves the unused bytes, and then applies padding.
- **Tag generation:** finalization XORs `K0` into `S2` and `K1` into `S3`, runs
  `p[12]`, XORs `K0` into `S3` and `K1` into `S4`, and serializes `S3 || S4`
  little-endian.
- **Tag verification:** only 16-byte tags are accepted. The complete expected
  tag is calculated and a dedicated full-scan comparison is used; normal
  `Bytes.equal` is not used on tags.
- **Unauthenticated plaintext:** decryption buffers the complete candidate,
  compares the tag, and returns the buffer only on success. Failure overwrites
  it on a best-effort basis and returns only `Authentication_failure`.
- **Exact key/nonce lengths:** abstract constructors accept exactly 16 bytes,
  make a defensive copy, and return `Invalid_length` otherwise.

## Hash and XOF lifecycle

- **Absorb-to-squeeze transition:** public absorbing and squeezing types are
  distinct. Once converted, a value cannot be passed to `absorb`.
- **Chunking:** persistent contexts keep up to seven pending bytes. Filling a
  block from multiple feeds is equivalent to a one-shot full block.
- **Partial squeeze blocks:** a squeezing state records an offset from 0 to 7;
  repeated calls continue at the next byte and permute after each complete
  output block.
- **Length handling:** one-shot XOF/CXOF lengths must be positive; negative and
  unrepresentable requested byte lengths return typed errors before allocation.
  A zero-length incremental squeeze is a documented no-op. Combined AEAD
  allocation checks for addition overflow. OCaml `bytes` bounds limit all input
  lengths to valid native integers.

## Areas requiring independent human attention

1. Compare the bitsliced S-box and rotations directly with Sec. 3 of final
   SP 800-232 and inspect native code on each intended compiler.
2. Review the AEAD last-block state replacement for every tail length 0–15.
3. Review OCaml compiler output and runtime behavior before making any stronger
   timing or side-channel statement.
4. Assess allocation volume, GC behavior, and secret lifetime for each target
   deployment.
5. Re-run all KATs and the differential harness from a clean checkout using a
   separately obtained official reference repository.
6. Add a real 32-bit runtime CI job when reliable hosted infrastructure is
   selected; the code is designed for it, but the initial hosted matrix does
   not execute on a 32-bit OCaml runtime.
