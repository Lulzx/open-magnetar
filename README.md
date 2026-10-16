# open-magnetar

[![CI](https://github.com/Lulzx/open-magnetar/actions/workflows/ci.yml/badge.svg)](https://github.com/Lulzx/open-magnetar/actions/workflows/ci.yml)
[![License: MIT OR Apache-2.0](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](#license)
![Rust: MSRV 1.90](https://img.shields.io/badge/rust-1.90%2B-orange.svg)

**A transparent, hash-based, post-quantum zkVM for RV64I — implemented from scratch in Rust, proved correct against an independent Python reference model, byte for byte.**

open-magnetar proves that a real C program ran correctly on a strict RV64I machine and produces a proof anyone can verify in tens of milliseconds — using only standard hash functions (SHA-256 by default). No elliptic curves, no trusted setup, no lattices, no algebraic hashes, and no conjectured proximity gaps at the default profile.

> Srinath Setty. *Magnetar: High-speed post-quantum RV64 zkVM from standard hashes.* 2026. [ePrint 2026/2423](https://eprint.iacr.org/2026/2423)

> **Disclaimer.** This project is not affiliated with, endorsed by, or derived from code by Microsoft or Microsoft Research. It is a clean-room re-implementation based on the public paper. Where the paper leaves details unspecified, this project makes its own choices, documented in [`docs/spec/`](docs/spec/). Performance and proof sizes will differ from those reported in the paper.

> **⚠️ Not audited. Do not use it to secure anything of value.** The proofs are not zero-knowledge: a proof reveals information about the execution. See [Security status](#security-status).

---

## Why this exists

Most zkVMs rest on elliptic-curve or lattice assumptions and a trusted or structured setup. Magnetar's bet is different: if your only cryptographic ingredient is a standard hash function, the system is transparent (nothing to set up, nothing to leak) and plausibly post-quantum. open-magnetar is an independent, fully open implementation of that design — specification first, then an executable Python reference model, then Rust — so every byte of every proof can be traced back to a written, testable specification.

## What works today

- **Real guests, proved end to end.** Strict-RV64I C programs are compiled with LLVM, executed, proved, and verified through the `om` CLI — including at the `provable-120` profile (120 bits of provable security, no grinding, no conjectured gaps).
- **Byte-identical cross-implementation agreement.** All 27 reference-vector files — including a complete end-to-end Fibonacci proof (15,630 bytes) and its verifying key — are reproduced byte for byte by the Rust crates. Two independent implementations agreeing on every byte is the strongest correctness signal available short of a formal proof.
- **A complete, written specification.** Sections 00–15 in [`docs/spec/`](docs/spec/) specify every component, mark every choice the paper does not dictate as **[OM-choice]**, and carry full soundness proofs where the original design needed them (including the §4.4a gap-amplification composition, proved in full).
- **All 15 of the paper's Table 1 workloads** exist as guests in [`guest/examples/`](guest/examples/) and pass 47 host-oracle execution cases.

| Suite | Result |
|---|---|
| Rust workspace (`cargo test --workspace`) | 331 tests, 0 failures |
| Python reference (`unittest discover`) | 223 tests, 0 failures |
| Reference vectors reproduced byte-for-byte | 27 / 27 files |
| Guest host-oracle executions | 47 cases, all pass |
| End-to-end acceptance at provable-120 | exactly 68 Mosaic claims (asserted) |

## Measured performance

Apple M4 Pro, release build, `A = 16`. Full methodology and the honest comparison with the paper are in [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

| Guest | Profile | Prove | Verify | Proof |
|---|---|---:|---:|---:|
| `fib(19)`, T = 256 | test | 0.95 s | 15 ms | 23,526 B |
| `fib(19)`, T = 256 | provable-120 | 0.81 s | 23 ms | 83,654 B |
| `sha256("abc")`, T = 8,192 | test | 61.7 s | 52 ms | 34,526 B |
| `erc20-transfer`, T = 512 | test | 1.40 s | 16 ms | 25,974 B |

The verifier is in the paper's ballpark. The prover is not — yet: it is the dense reference algorithm (parallelised with rayon for a 4–8× win, proofs unchanged), so its cost grows with the RAM address space rather than only with the trace length. The sparse, linear-in-T prover of [spec §7.10](docs/spec/07-twist-shout.md) is the main item of future work; it changes no transcript byte, no proof format, and no verifier code. A modelled T = 2²² proof (≈ 656 KiB) is in the paper's range but has not been measured at that size.

## Quick start

### Prove a Fibonacci execution in five commands

Requires a Rust toolchain (1.90+) and, for building guests, Homebrew LLVM/lld (`brew install llvm lld`).

```sh
export PATH=/opt/homebrew/opt/llvm/bin:/opt/homebrew/opt/lld/bin:$PATH
make -C guest clean && make -C guest A=16   # clean first if ELFs were built with another A
ABI="--ram-log-words 16 --input-log-words 14 --output-log-words 14"
cargo run -p om --release -- keygen --elf guest/examples/fib.elf --out /tmp/fib.vk $ABI
printf '\x13\0\0\0\0\0\0\0' > /tmp/in.bin    # input: u64 19
cargo run -p om --release -- prove --vk /tmp/fib.vk --elf guest/examples/fib.elf \
    --input /tmp/in.bin --out /tmp/fib.pf --instance /tmp/fib.inst
cargo run -p om --release -- verify --vk /tmp/fib.vk --instance /tmp/fib.inst --proof /tmp/fib.pf
# → OK
```

The `A`/`I`/`O` values must match between the guest link and `keygen`; `A = 16` keeps the current dense prover's memory use tractable (see [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md)).

### Run the test suites

```sh
cargo test --workspace                                       # Rust (includes vector conformance)
python3 -m unittest discover -s reference/tests -t reference # Python reference model (3.12+, stdlib only)
```

## How it works

A guest execution becomes two R1CS relations over a single bit-valued witness — one over GF(2), one over GF(2¹²⁸) — produced by a fetch-decode-execute circuit for strict RV64I. Virtual Spartan reduces both relations to one claim per witness segment; BinaryTwist and BinaryShout argue that registers, RAM, and bytecode were read and written consistently; a BinaryRouter handles shifts and sub-word stores. Everything is committed under a single MosaicPCS commitment (Ligerito over GF(2¹²⁸) with ring switching), opened at one point, and made non-interactive with a SHA-256 Fiat–Shamir transcript.

| Component | Role | Spec |
|---|---|---|
| Dual SIMD R1CS (GF(2) and GF(2¹²⁸)) over one bit-valued witness | CPU fetch-decode-execute | [06](docs/spec/06-spartan.md), [10](docs/spec/10-cpu-circuit.md) |
| Virtual Spartan | Reduces both relations to one claim per witness segment | [06](docs/spec/06-spartan.md) |
| BinaryTwist / BinaryShout | Register, RAM and bytecode consistency | [07](docs/spec/07-twist-shout.md) |
| BinaryRouter | Shifts and sub-word stores | [08](docs/spec/08-router.md) |
| MosaicPCS + ring switching + Ligerito | One commitment, one opening | [05](docs/spec/05-mosaic.md), [04](docs/spec/04-pcs.md) |
| SHA-256 Fiat–Shamir transcript | Non-interactive proofs | [02](docs/spec/02-transcript.md) |

**Design principles.** Proves RV64I executions (the M extension is planned later) · security rests only on standard hashes — SHA-256 by default, SHA3-256 and SHA-384 optional · 120 bits of provable security by default, with a per-round soundness ledger in [§13.2](docs/spec/13-security.md) · all arithmetic over GF(2) and GF(2¹²⁸) · no trusted setup of any kind.

## Repository layout

```
docs/spec/            normative specification (sections 00–15 + CONVENTIONS.md)
reference/            executable Python reference model (stdlib only)
  openmagnetar/       one module per protocol component, plus protocol.py (end to end)
  tests/              unit, sub-protocol, end-to-end and negative tests
  vectors/            JSON test vectors pinning every component's exact bytes
guest/                guest toolchain (linker script, runtime) and the 15 Table-1 workload guests
  rust/               custom RV64I target JSON for Rust guests (runtime crate: future work)
crates/               Rust workspace (16 crates, see below)
docs/BENCHMARKS.md    measured prover/verifier numbers vs the paper
papers/               source-paper PDFs for the §13.9 audit (gitignored; see README there)
```

The Rust workspace runs from the field up: `om-field` (GF(2¹²⁸) with PMULL/PCLMULQDQ), `om-transcript`, `om-sumcheck`, `om-pcs` (Merkle, additive NTT, Ligerito with `gs > 1`, ring switching, `Pcs` trait), `om-spartan`, `om-mosaic`, `om-memcheck`, `om-router`, `om-isa`, `om-circuit`, `om-elf`, `om-format`, `om-prover`, `om-verifier`, `om-sdk`, and the `om` CLI — all cryptography written from scratch. CI runs `fmt`, `clippy -D warnings`, the workspace tests (including vector conformance), and the Python suite.

## Security status

The default `provable-120` profile targets 120 bits of provable security per round under the random-oracle model for SHA-256, with the full error ledger in [spec §13](docs/spec/13-security.md). Known caveats, stated plainly:

- **Not audited.** No third party has reviewed this code or the specification.
- **Not zero-knowledge.** Proofs leak witness information; do not prove executions involving secrets.
- **Quantum caveat.** SHA-256 collision resistance against a quantum adversary is ≈ 85 bits (BHT); the `sha384` profile exists for ≈ 128-bit quantum collision resistance.
- **Prover side channels.** The prover is not constant-time.

The open audit items are tracked in [§13.9](docs/spec/13-security.md). Items 4–7 are resolved (checked against the Magnetar paper, proved in-spec, or re-derived and asserted by tests). Items 1–3 remain open **only** as bibliographic comparisons against the Ligerito, ring-switching, and Twist-and-Shout source papers — ePrint blocks automated PDF downloads, so the three PDFs are itemised in [`papers/README.md`](papers/README.md) for manual download; the internal correctness of those components is already established by in-spec proofs and cross-checks (see §13.9 for the narrowing notes per item).

## Roadmap

1. **Sparse prover** ([spec §7.10](docs/spec/07-twist-shout.md)) — linear-in-T proving instead of dense `T · 2^a` tables; the path to the paper's ~7M cycles/s class. No transcript, format, or verifier changes.
2. **Prove all 15 Table 1 workloads end to end** — today `fibonacci`, `sha256`, and `erc20-transfer` are proved; the other twelve are verified at execution level.
3. **Rust-language guests** — the [target JSON](guest/rust/riscv64i-open-magnetar-none-elf.json) is specified in [§14](docs/spec/14-guest-abi.md); the runtime crate (entry, panic handler, allocator, I/O helpers) is not yet written. C guests are the supported path today.
4. **Close §13.9 items 1–3** — blocked only on the three source PDFs listed in [`papers/README.md`](papers/README.md).
5. **Measure a T = 2²² proof** to replace the modelled ≈ 656 KiB figure with a measured one.

## Contributing

Contributions are welcome. The workflow that keeps two implementations byte-identical is: change the spec first, then the Python reference model and its vectors, then Rust, with tests at each step. Please run `cargo fmt --all`, `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`, and the Python suite before opening a pull request. Unless you explicitly state otherwise, any contribution you intentionally submit for inclusion shall be dual-licensed as below, without additional terms or conditions.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.
