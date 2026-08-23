# Security policy

## Supported versions

Until the first stable release, security fixes are made on the `main` branch.
After release, the latest minor release line will receive security fixes.

## Reporting a vulnerability

Please do not open a public issue for a suspected vulnerability. Use the
repository's **Security → Report a vulnerability** private advisory form. If
that channel is unavailable, email the maintainer at
<ville@vesilehto.fi>.

Include the affected version or commit, a minimal reproducer when possible,
the expected impact, and whether disclosure is time-sensitive. Receipt should
be acknowledged within seven days.

## Implementation status and caveats

- This is a pure OCaml implementation of final NIST SP 800-232. It is not an
  implementation of Ascon v1.2.
- Passing official vectors is evidence of conformance, not a security audit.
  This implementation has not received an independent cryptographic audit.
- It is not a FIPS-validated or NIST-validated cryptographic module.
- Authentication tags are compared without content-dependent early exit, but
  no formal constant-time guarantee is made for the OCaml compiler or runtime.
- The OCaml garbage collector can copy and retain ordinary heap values. Keys,
  plaintext, and intermediate values cannot be guaranteed to be zeroized.
- Callers must never reuse an Ascon-AEAD128 nonce with the same key.
- The public message API accepts whole bytes, not arbitrary bit-length inputs.
