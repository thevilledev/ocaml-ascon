# Changes

## 0.1.0 (unreleased)

- Implement Ascon-AEAD128 with detached and combined one-shot APIs.
- Implement one-shot and persistent incremental Ascon-Hash256.
- Implement typed absorb/squeeze APIs for Ascon-XOF128 and Ascon-CXOF128.
- Validate against the complete final SP 800-232 `ascon-c` KAT corpus.
- Add deterministic property tests, boundary tests, examples, benchmarks,
  odoc API documentation, opam metadata, and multi-version CI.
