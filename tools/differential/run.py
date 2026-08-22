#!/usr/bin/env python3
"""Compare randomized OCaml cases with the official ascon-c reference code."""

import argparse
import pathlib
import random
import subprocess
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[2]


def run(command, **kwargs):
    return subprocess.run(command, check=True, **kwargs)


def compile_reference(ascon_c, output_directory):
    tests = ascon_c / "tests"
    sources = [
        (
            "aead",
            ascon_c / "crypto_aead/asconaead128/ref",
            "aead.c",
            [
                "-Dcrypto_aead_encrypt=ref_aead_encrypt",
                "-Dcrypto_aead_decrypt=ref_aead_decrypt",
            ],
        ),
        (
            "hash",
            ascon_c / "crypto_hash/asconhash256/ref",
            "hash.c",
            ["-Dcrypto_hash=ref_hash"],
        ),
        (
            "xof",
            ascon_c / "crypto_hash/asconxof128/ref",
            "hash.c",
            ["-Dcrypto_hash=ref_xof"],
        ),
        (
            "cxof",
            ascon_c / "crypto_cxof/asconcxof128/ref",
            "hash.c",
            ["-Dcrypto_hash=ref_cxof_hash", "-Dcrypto_cxof=ref_cxof"],
        ),
    ]
    objects = []
    for name, include, source, defines in sources:
        target = output_directory / f"{name}.o"
        run(
            [
                "cc",
                "-std=c99",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                *defines,
                f"-I{include}",
                f"-I{tests}",
                "-c",
                str(include / source),
                "-o",
                str(target),
            ]
        )
        objects.append(target)
    executable = output_directory / "reference_driver"
    run(
        [
            "cc",
            "-std=c99",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            str(ROOT / "tools/differential/reference_driver.c"),
            *(str(obj) for obj in objects),
            "-o",
            str(executable),
        ]
    )
    return executable


def output(command):
    return subprocess.check_output(command, text=True).strip()


def random_hex(rng, length):
    return bytes(rng.randrange(256) for _ in range(length)).hex()


def compare(reference, ocaml, arguments, reference_arguments=None):
    expected = output([str(reference), *(reference_arguments or arguments)])
    actual = output([str(ocaml), *arguments])
    if expected != actual:
        raise RuntimeError(f"mismatch for: {' '.join(arguments)}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("ascon_c", type=pathlib.Path)
    parser.add_argument("--cases", type=int, default=100)
    arguments = parser.parse_args()
    ascon_c = arguments.ascon_c.resolve()
    run(["dune", "build", "tools/differential/ocaml_driver.exe"], cwd=ROOT)
    ocaml = ROOT / "_build/default/tools/differential/ocaml_driver.exe"
    rng = random.Random(0x800232)
    boundaries = [0, 1, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65]
    with tempfile.TemporaryDirectory(prefix="ascon-differential-") as temporary:
        reference = compile_reference(ascon_c, pathlib.Path(temporary))
        for case in range(arguments.cases):
            message_length = rng.choice(boundaries) if case < len(boundaries) else rng.randrange(258)
            ad_length = rng.choice(boundaries) if case < len(boundaries) else rng.randrange(258)
            key = random_hex(rng, 16)
            nonce = random_hex(rng, 16)
            ad = random_hex(rng, ad_length)
            message = random_hex(rng, message_length)
            compare(reference, ocaml, ["aead", key, nonce, ad, message])
            compare(reference, ocaml, ["hash", message])
            xof_length = rng.randrange(1, 65)
            expected_xof = output([str(reference), "xof", message])[: 2 * xof_length]
            actual_xof = output([str(ocaml), "xof", message, str(xof_length)])
            if expected_xof != actual_xof:
                raise RuntimeError(f"XOF mismatch in case {case}")
            customization = random_hex(rng, rng.randrange(257))
            output_length = rng.randrange(1, 97)
            compare(
                reference,
                ocaml,
                ["cxof", customization, message, str(output_length)],
            )
    print(f"Differential: {arguments.cases} randomized cases per algorithm passed")


if __name__ == "__main__":
    main()
