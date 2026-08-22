# Official SP 800-232 known-answer tests

These four files are copied byte-for-byte from the official
[`ascon/ascon-c`](https://github.com/ascon/ascon-c) repository at commit
`446347f21b209f3921c65ece70027c366cbe1693`:

- `crypto_aead/asconaead128/LWC_AEAD_KAT_128_128.txt`
- `crypto_hash/asconhash256/LWC_HASH_KAT_128_256.txt`
- `crypto_hash/asconxof128/LWC_XOF_KAT_128_512.txt`
- `crypto_cxof/asconcxof128/LWC_CXOF_KAT_128_512.txt`

The upstream project identifies these as the new NIST SP 800-232 vectors. Its
older v1.2 vectors are deliberately not included. The files are provided by the
Ascon team under CC0 1.0 Universal; see `LICENSE` in this directory.
