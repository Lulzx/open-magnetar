# open-magnetar

[![CI](https://github.com/Lulzx/open-magnetar/actions/workflows/ci.yml/badge.svg)](https://github.com/Lulzx/open-magnetar/actions/workflows/ci.yml)
[![License: MIT OR Apache-2.0](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](#license)
![Rust: MSRV 1.90](https://img.shields.io/badge/rust-1.90%2B-orange.svg)

open-magnetar is a zkVM for RV64I. It proves that a C program executed correctly and produces a proof that a verifier can check in tens of milliseconds. The cryptography uses standard hash functions only, SHA-256 by default. There are no elliptic curves, no trusted setup, and no lattice assumptions. At the default profile there are also no conjectured proximity gaps. The implementation is written in Rust and checked against an independent reference model in Python. The two implementations produce identical proof bytes.

> Srinath Setty. *Magnetar: High-speed post-quantum RV64 zkVM from standard hashes.* 2026. [ePrint 2026/2423](https://eprint.iacr.org/2026/2423)

> Disclaimer. This project is not affiliated with Microsoft or Microsoft Research and is not derived from their code. It is a clean room reimplementation of the public paper. Where the paper does not specify a detail, this project chooses one and records the choice in [`docs/spec/`](docs/spec/). Performance and proof sizes will differ from the paper.

> Not audited. Do not use this to secure anything of value. The proofs are not zero knowledge. A proof reveals information about the execution. See [Security status](#security-status).

## Background

Most zkVMs depend on elliptic curve or lattice assumptions and on some form of setup. Magnetar takes a different approach. If the only cryptographic primitive is a standard hash function, the system needs no setup and is plausibly post quantum. open-magnetar implements that design in the open. Work started with a written specification, then an executable model in Python, then the Rust implementation. Each proof byte can be traced back to the specification.

## Current state

C guests for strict RV64I are built with LLVM, then executed, proved, and verified with the `om` CLI. This works at the `provable-120` profile as well as at the smaller test profile. `provable-120` means 120 bits of provable security per round, with no grinding and no conjectured gaps.

All 27 files in `reference/vectors/` are reproduced byte for byte by the Rust crates. That includes a complete Fibonacci proof of 15,630 bytes and its verifying key. Agreement between two independent implementations is the main correctness check used in this project, short of a formal proof.

The specification in [`docs/spec/`](docs/spec/) covers sections 00 to 15. Choices that the paper does not dictate are marked **[OM-choice]**. Section 04 §4.4a contains a full soundness proof for the gap amplification composition used by the `provable-120` parameters.

All 15 workloads from Table 1 of the paper are present as guests in [`guest/examples/`](guest/examples/) and pass 47 execution cases against a Python oracle.

| Suite | Result |
|---|---|
| Rust workspace, `cargo test --workspace` | 331 tests, 0 failures |
| Python reference model | 223 tests, 0 failures |
| Reference vectors | 27 of 27 files reproduced byte for byte |
| Guest execution cases | 47 cases, all pass |
| Acceptance test at `provable-120` | exactly 68 Mosaic claims, asserted in tests |

## Benchmarks

Measured on an Apple M4 Pro with a release build and `A = 16`. Method and comparison with the paper are in [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

| Guest | Profile | Prove | Verify | Proof |
|---|---|---:|---:|---:|
| `fib(19)`, T = 256 | test | 0.95 s | 15 ms | 23,526 B |
| `fib(19)`, T = 256 | provable-120 | 0.81 s | 23 ms | 83,654 B |
| `sha256("abc")`, T = 8,192 | test | 61.7 s | 52 ms | 34,526 B |
| `erc20-transfer`, T = 512 | test | 1.40 s | 16 ms | 25,974 B |

Verifier time is close to the numbers in the paper. Prover time is not, though the gap is smaller than it was. The Twist read and write sum check now uses the sparse algorithm of [spec §7.10](docs/spec/07-twist-shout.md) in the Rust prover, so it no longer builds tables of size `T · 2^a`. Proof bytes are unchanged. Workloads at T = 32,768 and T = 65,536 that previously ran out of memory now prove in tens of seconds. The Spartan witness handling and the Mosaic commitment tables are still dense in T, which is what limits large traces now. A proof at T = 2²² is modelled at about 656 KiB, close to the paper, but has not been measured at that size. Measured numbers are in [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

## Quick start

You need Rust 1.90 or later. Building guests also needs LLVM and lld, for example `brew install llvm lld` on macOS.

```sh
export PATH=/opt/homebrew/opt/llvm/bin:/opt/homebrew/opt/lld/bin:$PATH
make -C guest clean && make -C guest A=16   # clean first if ELFs were built with another A
ABI="--ram-log-words 16 --input-log-words 14 --output-log-words 14"
cargo run -p om --release -- keygen --elf guest/examples/fib.elf --out /tmp/fib.vk $ABI
printf '\x13\0\0\0\0\0\0\0' > /tmp/in.bin    # input: u64 19
cargo run -p om --release -- prove --vk /tmp/fib.vk --elf guest/examples/fib.elf \
    --input /tmp/in.bin --out /tmp/fib.pf --instance /tmp/fib.inst
cargo run -p om --release -- verify --vk /tmp/fib.vk --instance /tmp/fib.inst --proof /tmp/fib.pf
# prints OK
```

The values of A, I, and O at guest build time must match the values passed to `keygen`. A = 16 keeps memory use reasonable for the current dense prover. See [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

Test suites:

```sh
cargo test --workspace                                       # Rust, includes vector conformance
python3 -m unittest discover -s reference/tests -t reference # Python reference model, 3.12+, stdlib only
```

## How it works

A guest execution is encoded as two R1CS relations over one bit valued witness. One relation is over GF(2) and the other is over GF(2¹²⁸). Both come from a circuit that fetches, decodes, and executes strict RV64I instructions. Virtual Spartan reduces the two relations to one claim per witness segment. BinaryTwist and BinaryShout argue that registers, RAM, and bytecode were read and written consistently. A BinaryRouter handles shifts and sub word stores. All witness segments are committed under one MosaicPCS commitment, which uses Ligerito over GF(2¹²⁸) with ring switching, and opened at a single point. A SHA-256 Fiat Shamir transcript makes the proof non interactive.

| Component | Role | Spec |
|---|---|---|
| Dual SIMD R1CS over GF(2) and GF(2¹²⁸), one witness | CPU fetch, decode, execute | [06](docs/spec/06-spartan.md), [10](docs/spec/10-cpu-circuit.md) |
| Virtual Spartan | Reduces both relations to one claim per witness segment | [06](docs/spec/06-spartan.md) |
| BinaryTwist and BinaryShout | Register, RAM, and bytecode consistency | [07](docs/spec/07-twist-shout.md) |
| BinaryRouter | Shifts and sub word stores | [08](docs/spec/08-router.md) |
| MosaicPCS, ring switching, Ligerito | One commitment, one opening | [05](docs/spec/05-mosaic.md), [04](docs/spec/04-pcs.md) |
| SHA-256 Fiat Shamir transcript | Makes the proof non interactive | [02](docs/spec/02-transcript.md) |

Scope for version 1 is RV64I only. The M extension is planned later. The default profile aims at 120 bits of provable security. The per round error ledger is in [§13.2](docs/spec/13-security.md). All arithmetic is over GF(2) and GF(2¹²⁸). SHA3-256 and SHA-384 are available as options next to the SHA-256 default.

## Repository layout

```
docs/spec/            normative specification, sections 00 to 15 plus CONVENTIONS.md
reference/            executable Python reference model, stdlib only
  openmagnetar/       one module per protocol component, plus protocol.py for the full protocol
  tests/              unit tests, sub protocol tests, end to end tests, negative tests
  vectors/            JSON test vectors that pin the exact bytes of each component
guest/                guest toolchain and the 15 Table 1 workload guests
  rust/               Rust guests: target JSON, om-guest runtime crate, examples, Makefile
crates/               Rust workspace, 16 crates, listed below
docs/BENCHMARKS.md    measured prover and verifier numbers, with comparison to the paper
papers/               source paper PDFs for the §13.9 audit, gitignored, see the README there
```

The Rust crates start at the field and go up to the CLI. `om-field` implements GF(2¹²⁸) with PMULL and PCLMULQDQ. Then come `om-transcript`, `om-sumcheck`, `om-pcs` with Merkle trees, an additive NTT, Ligerito with `gs > 1`, ring switching, and a `Pcs` trait. The remaining crates are `om-spartan`, `om-mosaic`, `om-memcheck`, `om-router`, `om-isa`, `om-circuit`, `om-elf`, `om-format`, `om-prover`, `om-verifier`, `om-sdk`, and the `om` CLI. All cryptography is written from scratch in this repository. CI runs `cargo fmt`, clippy with `-D warnings`, the Rust tests including vector conformance, and the Python test suite.

## Security status

The default `provable-120` profile targets 120 bits of provable security per round. The analysis treats SHA-256 as a random oracle. The full error ledger is in [spec §13](docs/spec/13-security.md).

No third party has audited this code or the specification. The system is not zero knowledge, so proofs leak information about the execution and about any data the guest handled. Do not prove executions that involve secrets. Against a quantum adversary, SHA-256 collision resistance is about 85 bits by the BHT bound. The `sha384` profile raises that to about 128 bits. The prover is not constant time.

Open audit items are tracked in [§13.9](docs/spec/13-security.md). Items 4 to 7 are resolved. They were checked against the Magnetar paper, proved inside the specification, or rederived and then asserted by tests. Items 1 to 3 are still open, but only as comparisons against the source papers for Ligerito, ring switching, and Twist and Shout. ePrint blocks automated PDF downloads, so [`papers/README.md`](papers/README.md) lists the three files to download by hand. The internal correctness of those components does not depend on that comparison. It rests on proofs in the specification and on tests. Section 13.9 records, item by item, what has already been checked and what has not.

## Roadmap

1. Sparse handling for the Spartan witness and the Mosaic commitment tables. The Twist part of [spec §7.10](docs/spec/07-twist-shout.md) is implemented, and proof bytes did not change. What still grows with large constants in T is the witness and commitment side. That is the remaining path toward the proving throughput reported in the paper, about 7M cycles per second, and toward proving at T = 2²² on ordinary hardware.
2. Prove the last Table 1 workload, `radix-sort-u64`. Fourteen of the fifteen are proved now. A proof attempt at T = 2²² was killed by the OS at 10.2 GiB resident memory, in the Spartan and Mosaic parts rather than in Twist. It waits on item 1. Details are in [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).
3. Rust guests. Done for the basic path. The runtime crate `guest/rust/om-guest` provides the entry point, a bump allocator, and I/O helpers, and the Fibonacci example in `guest/rust/examples/fib` is proved and verified end to end. Build it with `make -C guest/rust`. See [§14](docs/spec/14-guest-abi.md). More Rust examples would still be useful.
4. Close §13.9 items 1 to 3. The Ligerito paper has been obtained and its `t` derivation compared. The ring switching and Twist and Shout papers are still blocked on manual download. See [`papers/README.md`](papers/README.md).
5. Measure a proof at T = 2²² and replace the modelled size of about 656 KiB with a measured one.

## Contributing

Contributions are welcome. To keep the two implementations in agreement, change the specification first, then the Python reference model and its vectors, then the Rust code, with tests at each step. Before opening a pull request, run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`, and the Python suite. Unless you state otherwise, contributions are dual licensed under the terms below.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
