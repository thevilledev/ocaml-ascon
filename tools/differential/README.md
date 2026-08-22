# Developer differential test

This optional harness compares randomized OCaml results against the official
NIST SP 800-232 reference implementations in `ascon/ascon-c`. It builds the C
code only in a temporary directory; neither the library nor its normal tests
have a C dependency.

From the repository root:

```sh
python3 tools/differential/run.py /path/to/ascon-c --cases 100
```

The harness covers random keys, nonces, associated data, messages,
customizations, and XOF output lengths. Its PRNG seed is fixed so failures are
reproducible. The C checkout is not downloaded automatically.
