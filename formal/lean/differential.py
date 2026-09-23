#!/usr/bin/env python3
"""Compare the OCaml library with the Lean specification on random inputs.

The OCaml side is `tools/differential/ocaml_driver.exe`. The Lean side is the
executable specification (`lake exe spec-driver`), which is proved equal to
the Lean model of the OCaml code and checked against the official KAT files.
This harness goes beyond the KAT ranges: every rate boundary, associated data
and messages up to 300 bytes, customizations up to the 256-byte limit, and
output lengths up to 300 bytes.
"""

import argparse
import pathlib
import random
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BOUNDARIES = [0, 1, 7, 8, 9, 15, 16, 17, 23, 24, 25, 31, 32, 33, 63, 64, 65]


def build():
    subprocess.run(["dune", "build", "--root", str(ROOT), "tools/differential/ocaml_driver.exe"],
                   cwd=ROOT, check=True)
    subprocess.run(["lake", "build", "spec-driver"], cwd=HERE, check=True,
                   stdout=subprocess.DEVNULL)
    return (ROOT / "_build/default/tools/differential/ocaml_driver.exe",
            HERE / ".lake/build/bin/spec-driver")


def random_hex(rng, length):
    return bytes(rng.randrange(256) for _ in range(length)).hex()


def cases(rng, count):
    """Yield command argument lists; the first cases enumerate every boundary."""
    lengths = [(a, b) for a in BOUNDARIES for b in BOUNDARIES]
    for index in range(count):
        if index < len(lengths):
            ad_length, message_length = lengths[index]
        else:
            ad_length, message_length = rng.randrange(301), rng.randrange(301)
        key, nonce = random_hex(rng, 16), random_hex(rng, 16)
        ad, message = random_hex(rng, ad_length), random_hex(rng, message_length)
        yield ["aead", key, nonce, ad, message]
        yield ["hash", message]
        yield ["xof", message, str(rng.choice(BOUNDARIES[1:] + [rng.randrange(1, 301)]))]
        customization = random_hex(rng, rng.choice([0, 1, 8, 255, 256, rng.randrange(257)]))
        yield ["cxof", customization, message, str(rng.randrange(1, 301))]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", type=int, default=400)
    parser.add_argument("--seed", type=int, default=0x800232)
    arguments = parser.parse_args()
    ocaml, spec = build()
    rng = random.Random(arguments.seed)
    commands = list(cases(rng, arguments.cases))
    spec_input = "\n".join(" ".join(a if a else "-" for a in c) for c in commands) + "\n"
    spec_output = subprocess.run([str(spec)], input=spec_input, text=True, check=True,
                                 capture_output=True).stdout.splitlines()
    if len(spec_output) != len(commands):
        raise SystemExit("specification driver produced the wrong number of lines")
    for command, expected in zip(commands, spec_output):
        actual = subprocess.run([str(ocaml), *command], text=True, check=True,
                                capture_output=True).stdout.strip()
        if actual != expected:
            raise SystemExit(f"MISMATCH for {' '.join(command)}\n  OCaml: {actual}\n  Lean:  {expected}")
    print(f"Differential: {len(commands)} OCaml results equal the Lean specification "
          f"({arguments.cases} cases of AEAD, Hash256, XOF128 and CXOF128)")


if __name__ == "__main__":
    main()
