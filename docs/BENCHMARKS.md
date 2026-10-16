# Benchmarks

Measured 2026-10-16 on an Apple M4 Pro (24 GiB RAM), Rust release build
(`cargo build -p om --release`, thin LTO), unless stated otherwise. These
numbers are for the implementation as it stands: correct and byte-compatible
with the Python reference model, but with a deliberately straightforward
prover (see "Why the prover is slower than the paper" below).

Guests were built with the Homebrew LLVM toolchain (`brew install llvm lld`,
see `guest/Makefile`) and proved through the `om` CLI with
`Params(ram_log_words=16, input=14, output=14)` (spec 14 defaults; the guest
ELFs for these runs were linked with `A=16` region bases to match).

## End-to-end guests (proved and verified)

| Guest | Profile | T (cycles) | Prove | Verify | Proof size |
|---|---|---|---|---|---|
| fibonacci, fib(19) = 4181 | test (t = 8) | 256 | 0.95 s | 15 ms | 23,526 B |
| fibonacci, fib(19) = 4181 | provable-120 (t = 177, gs = 2) | 256 | 0.81 s | 23 ms | 83,654 B |
| sha256 of `"abc"` | test (t = 8) | 8,192 | 61.7 s | 52 ms | 34,526 B |
| erc20-transfer (3 accounts) | test (t = 8) | 512 | 1.40 s | 16 ms | 25,974 B |

Outputs were checked independently (fib value, SHA-256 digest `ba7816bf…`,
post-transfer balances 70/80).

### Further Table 1 workloads proved 2026-10-16

Eight more guests were proved and verified end to end through the `om` CLI
(test profile, `A = 16`), with outputs checked against `om run`:

| Guest | T (cycles) | Proof size |
|---|---|---|
| hot-cell-increment (100 iterations from 41) | 1,024 | 27,558 B |
| stream-copy (28 bytes) | 256 | 23,622 B |
| pointer-chase (16 nodes, 20 steps) | 1,024 | 27,590 B |
| binary-search (8 keys, 2 queries) | 512 | 25,462 B |
| varint-decode (3 values) | 512 | 25,558 B |
| lz4-decode (one match sequence) | 256 | 23,494 B |
| erc20-transfer-from (3 accounts) | 1,024 | 27,894 B |
| erc20-mixed-block (3 accounts, 2 transfers) | 512 | 25,878 B |

That makes 11 of the 15 Table 1 workloads proved end to end. The four not
yet proved are `keccak-f1600`, `sha256-merkle-path`, `evm-erc20-transfer`,
and `radix-sort-u64`. With the current dense prover these are not small
jobs: a `sha256-merkle-path` attempt at `A = 16` was killed by the OS for
memory use, and a `keccak-f1600` attempt was stopped for the same reason.
The dense tables grow with `T · 2^a`, so large traces need the sparse
prover of spec 07.10 before they are practical to prove on a laptop.
`radix-sort-u64` also needs a larger `A` at load time, because its static
buffers (about 384 KiB) do not fit under the I/O window at `A = 16`. All
four still pass their host-oracle execution cases.

## Test suites

| Suite | Count | Wall time (debug) |
|---|---|---|
| Rust workspace (`cargo test --workspace`) | 331 tests, 0 failures | ~1 min |
| Python reference (`unittest discover`) | 223 tests, 0 failures | 114 s |
| Guest oracle executions (Python harness) | 47 cases, all pass | ~1 min |

Every `reference/vectors/**/*.json` file (27 files) is reproduced
byte-for-byte by the corresponding Rust crate's tests, including the
end-to-end Fibonacci proof (15,630 bytes) and its verifying key.

## Proof-size model at scale (not measured at that size)

From `params.proof_size_bytes` (spec 04.7 / 13.5), provable-120 profile:

| `n_pack` | Ligerito opening |
|---|---|
| 20 | 357 KiB |
| 22 | 415 KiB |
| 24 | 509 KiB |
| 26 (T = 2^22 machine) | 624 KiB, ≈ 656 KiB whole proof |

The paper reports at most 599 KiB for the whole proof, so the model is in the
paper's range. Treat absolute values as estimates (±15%) until a T = 2^22
proof is actually generated and measured.

## Comparison with the paper, honestly

| Quantity | Paper (Magnetar) | This implementation |
|---|---|---|
| Proving throughput | ~1.45 M fib steps/s (≈ 7 M cycles/s class) | ~10^2–10^3 cycles/s at small T (see below) |
| Proof size | ≤ 599 KiB | 84 KiB measured at T = 256; ≈ 656 KiB modelled at T = 2^22 |
| Verifier time | ~13 ms | 14–52 ms measured at the sizes above |

The verifier is in the paper's ballpark. The prover is not — by orders of
magnitude — for a structural reason: both the Python reference model and this
faithful Rust port materialise the dense `T · 2^a` tables of the Twist
read/write sum-check (spec 07.5), so proving cost grows with the RAM address
space (`2^a`), not just with the trace. The paper's prover (and spec 07.10,
which is informative only) uses a sparse, linear-in-T algorithm. Closing that
gap means implementing the sparse prover algorithms of 07.10 (and analogous
sparsity in Shout/Spartan witness handling); the transcript, proof format and
verifier would not change. A rayon pass over the dense hot loops (sum-check
rounds, table construction, Ligerito row encodes, Merkle layers) already gave
4–8× (sha256 prove: 510 s → 62 s) with bit-identical proofs, which is the
current state of optimisation: parallel, but asymptotically the reference
algorithm.

Other paper comparisons: security is the 120-bit provable profile by default
(no conjectured proximity gaps, no grinding), SHA-256 by default, strict
RV64I only, no zero-knowledge and no recursion — matching the v1 scope of
`docs/spec/`.
