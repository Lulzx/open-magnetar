# open-magnetar

`open-magnetar` is a clean-room implementation of the [Magnetar](https://eprint.iacr.org/2026/2423) RV64I zkVM in Rust and Python. It proves the execution of strict RV64I ELF binaries using only standard hash functions (SHA-256 by default, SHA3-256 and SHA-384 optional) and arithmetic over `GF(2)` and `GF(2^128)`.

## Features

- **Standard hashes only**: no elliptic curves, lattices, or trusted setup.
- **120-bit provable security** (`provable-120` profile): unique-decoding proximity bounds with gap amplification (`g_s = 2`), no conjectured gaps, no grinding ([spec §04.4a](docs/spec/04-pcs.md), [§13](docs/spec/13-security.md)).
- **Architecture**: dual SIMD R1CS over `GF(2)` and `GF(2^128)` on a shared bit-witness, reduced via Virtual Spartan ([§06](docs/spec/06-spartan.md), [§10](docs/spec/10-cpu-circuit.md)); BinaryTwist and BinaryShout for register, RAM, and ROM consistency ([§07](docs/spec/07-twist-shout.md)); BinaryRouter for shifts and sub-word stores ([§08](docs/spec/08-router.md)); single commitment and opening via MosaicPCS, ring switching, and Ligerito ([§04](docs/spec/04-pcs.md), [§05](docs/spec/05-mosaic.md)).
- **Bit-exact cross-verification**: normative specification ([`docs/spec/`](docs/spec/)), zero-dependency Python reference model ([`reference/`](reference/)), and 16-crate Rust workspace ([`crates/`](crates/)) agree byte-for-byte across all 27 test vector files.
- **Guest support**: C (`clang --target=riscv64`) and Rust (`no_std` via `guest/rust/om-guest`) guests; all 15 workloads from Table 1 of the paper are proved and verified end-to-end.

## Build and Usage

Requires Rust 1.90+, Python 3.12+ (for reference tests), and LLVM + `lld` (to build RV64I guests).

```sh
# Run Rust and Python test suites (346 Rust tests, 223 Python tests, 27 vector files)
cargo test --workspace --release
python3 -m unittest discover -s reference/tests -t reference

# Build C guest examples (A = log2(RAM words), I = log2(input words), O = log2(output words))
export PATH=/opt/homebrew/opt/llvm/bin:/opt/homebrew/opt/lld/bin:$PATH
make -C guest clean && make -C guest A=16

# Keygen, prove, and verify fib(19)
ABI="--ram-log-words 16 --input-log-words 14 --output-log-words 14"
cargo run -p om --release -- keygen --elf guest/examples/fib.elf --out /tmp/fib.vk $ABI
printf '\x13\0\0\0\0\0\0\0' > /tmp/in.bin
cargo run -p om --release -- prove --vk /tmp/fib.vk --elf guest/examples/fib.elf \
    --input /tmp/in.bin --out /tmp/fib.pf --instance /tmp/fib.inst
cargo run -p om --release -- verify --vk /tmp/fib.vk --instance /tmp/fib.inst --proof /tmp/fib.pf
```

Pass `--profile provable-120` to `keygen` for full 120-bit provable security (default is `test`). Set `OM_TRACE=1` to print per-phase timing and heap usage.

## Benchmarks

Apple M4 Pro (14-core, 24 GiB), `rustc` release build, `A = 16` unless noted. Full breakdown in [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md).

| Guest | Cycles (`T`) | Profile | Prove | Peak RSS | Verify | Proof Size |
|---|---:|---|---:|---:|---:|---:|
| `fib(19)` | `2^8` | test | 0.03 s | 16 MiB | 10 ms | 23,526 B |
| `fib(19)` | `2^8` | provable-120 | 0.03 s | 23 MiB | 20 ms | 83,654 B |
| `erc20-transfer` | `2^9` | test | 0.03 s | 18 MiB | 10 ms | 25,398 B |
| `sha256("abc")` | `2^13` | test | 0.15 s | 41 MiB | 10 ms | 34,526 B |
| `keccak-f1600` | `2^15` | test | 0.27 s | 112 MiB | 10 ms | 39,806 B |
| `keccak-f1600` | `2^15` | provable-120 | 0.27 s | 121 MiB | 30 ms | 289,406 B |
| `radix-sort-u64` (`A = 17`) | `2^22` | test | 20.8 s | 7.7 GiB | 20 ms | 60,806 B |
| `radix-sort-u64` (`A = 17`) | `2^22` | provable-120 | 21.6 s | 8.2 GiB | 60 ms | 603,942 B (589.8 KiB) |

At `T = 2^22`, throughput is ~202k cycles/s (`test`) and ~194k cycles/s (`provable-120`), using hardware `PMULL`/`PCLMULQDQ` field arithmetic, ARMv8 SHA-256 intrinsics, column-major coset NTTs, compiled word-mask Spartan evaluation, and packed bit witnesses.

## Directory Layout

```
crates/               Rust workspace (om-field, om-transcript, om-sumcheck, om-pcs,
                      om-mosaic, om-spartan, om-memcheck, om-router, om-isa,
                      om-circuit, om-elf, om-format, om-prover, om-verifier, om-sdk, om)
docs/spec/            Specification (00-overview .. 15-testing, CONVENTIONS.md)
docs/BENCHMARKS.md    Prover/verifier benchmarks and memory profiles
guest/                C and Rust RV64I guest runtime and 15 benchmark programs
reference/            Self-contained Python reference implementation and JSON test vectors
```

## Notes and Limitations

- **Unaudited**: experimental research code; do not use in production.
- **Not zero-knowledge**: proofs reveal information about the execution trace and witness. Do not prove secret inputs.
- **ISA scope**: strict RV64I (no `M`/`A`/`F`/`D`/`C` extensions).
- **Post-quantum hash bound**: SHA-256 provides ~85-bit quantum collision resistance (BHT bound); use `--hash sha384` for ~128-bit quantum collision resistance.
- **Attribution**: independent implementation of Setty ([ePrint 2026/2423](https://eprint.iacr.org/2026/2423)); not affiliated with or derived from Microsoft Research. Protocol details left unspecified by the paper are documented as **[OM-choice]** in [`docs/spec/`](docs/spec/).

## License

Dual-licensed under [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT).
